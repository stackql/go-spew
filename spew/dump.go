/*
 * Copyright (c) 2013-2016 Dave Collins <dave@davec.name>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

package spew

import (
	"bytes"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"reflect"
	"regexp"
	"strconv"
	"strings"
)

var (
	// uint8Type is a reflect.Type representing a uint8.  It is used to
	// convert cgo types to uint8 slices for hexdumping.
	uint8Type = reflect.TypeOf(uint8(0))

	// cCharRE is a regular expression that matches a cgo char.
	// It is used to detect character arrays to hexdump them.
	cCharRE = regexp.MustCompile(`^.*\._Ctype_char$`)

	// cUnsignedCharRE is a regular expression that matches a cgo unsigned
	// char.  It is used to detect unsigned character arrays to hexdump
	// them.
	cUnsignedCharRE = regexp.MustCompile(`^.*\._Ctype_unsignedchar$`)

	// cUint8tCharRE is a regular expression that matches a cgo uint8_t.
	// It is used to detect uint8_t arrays to hexdump them.
	cUint8tCharRE = regexp.MustCompile(`^.*\._Ctype_uint8_t$`)
)

// dumpState contains information about the state of a dump operation.
type dumpState struct {
	w                io.Writer
	depth            int
	pointers         map[uintptr]int
	pointerDefs      map[uintptr]reflect.Value
	ignoreNextType   bool
	ignoreNextIndent bool
	pointerAccrual   bool
	referenceFilling bool
	cs               *ConfigState
}

// indent performs indentation according to the depth level and cs.Indent
// option.
func (d *dumpState) indent() {
	if d.pointerAccrual {
		return
	}
	if d.ignoreNextIndent {
		d.ignoreNextIndent = false
		return
	}
	d.write(bytes.Repeat([]byte(d.cs.Indent), d.depth))
}

func (d *dumpState) generatePointerVarName(addr uintptr) string {
	return fmt.Sprintf("PtrVar_%#x", addr)
}

// unpackValue returns values inside of non-nil interfaces when possible.
// This is useful for data types like structs, arrays, slices, and maps which
// can contain varying types packed inside an interface.
func (d *dumpState) unpackValue(v reflect.Value) reflect.Value {
	if v.Kind() == reflect.Interface && !v.IsNil() {
		v = v.Elem()
	}
	return v
}

// dumpPtr handles formatting of pointers by indirecting them as necessary.
func (d *dumpState) dumpPtr(v reflect.Value) {
	// Remove pointers at or below the current depth from map used to detect
	// circular refs.
	for k, depth := range d.pointers {
		if depth >= d.depth {
			delete(d.pointers, k)
		}
	}

	var isOriginOfPointerAccrual bool

	// Keep list of all dereferenced pointers to show later.
	pointerChain := make([]uintptr, 0)

	// Figure out how many levels of indirection there are by dereferencing
	// pointers and unpacking interfaces down the chain while detecting circular
	// references.
	nilFound := false
	cycleFound := false
	ptrOutOfLine := false
	indirects := 0
	ve := v
	var finalAddr *uintptr
	for ve.Kind() == reflect.Ptr {
		if ve.IsNil() {
			nilFound = true
			break
		}
		indirects++
		addr := ve.Pointer()
		finalAddr = &addr
		pointerChain = append(pointerChain, addr)
		if pd, ok := d.pointers[addr]; ok && pd < d.depth {
			cycleFound = true
			indirects--
			break
		}
		d.pointers[addr] = d.depth

		ve = ve.Elem()
		if ve.Kind() == reflect.Interface {
			if ve.IsNil() {
				nilFound = true
				break
			}
			ve = ve.Elem()
		}
	}
	if finalAddr != nil && !nilFound {
		_, ok := d.pointerDefs[*finalAddr]
		if ok {
		} else {
			d.pointerDefs[*finalAddr] = ve
		}
		ptrOutOfLine = true
	}

	// Display type information.
	if d.cs.AsGolangSource {
		if !nilFound {
			if finalAddr != nil {
				d.write([]byte(d.generatePointerVarName(*finalAddr)))
				if d.referenceFilling {
					return
				}
				if !d.pointerAccrual {
					d.pointerAccrual = true
					isOriginOfPointerAccrual = true
				}
			} else if isInlineInitializable(ve) {
				d.write(ampersandBytes)
				d.write([]byte(strings.TrimLeft(ve.Type().String(), "*")))
			} else {
				d.write(ampersandBytes)
				d.write([]byte("[]" + strings.TrimLeft(ve.Type().String(), "*")))
				d.write(openBraceBytes)
			}
		}
	} else {
		d.write(openParenBytes)
		d.write(bytes.Repeat(asteriskBytes, indirects))
		d.write([]byte(ve.Type().String()))
		d.write(closeParenBytes)
	}

	// Display pointer information.
	if !d.cs.DisablePointerAddresses && len(pointerChain) > 0 {
		d.write(openParenBytes)
		for i, addr := range pointerChain {
			if i > 0 {
				d.write(pointerChainBytes)
			}
			d.cs.PrintHexPtr(d.w, addr)
		}
		d.write(closeParenBytes)
	}

	// Display dereferenced value.
	if !d.cs.AsGolangSource {
		d.write(openParenBytes)
	}
	switch {
	case nilFound:
		d.write(d.cs.GetNilBytes())

	case cycleFound:
		d.write(circularBytes)

	default:
		d.ignoreNextType = true
		d.dump(ve)
		if isOriginOfPointerAccrual {
			d.pointerAccrual = false
		}
	}
	if !d.cs.AsGolangSource {
		d.write(closeParenBytes)
		return
	}
	if !isInlineInitializable(ve) && !ptrOutOfLine {
		d.write(closeBraceBytes)
		d.write([]byte("[0]"))
	}
}

// dumpSlice handles formatting of arrays and slices.  Byte (uint8 under
// reflection) arrays and slices are dumped in hexdump -C fashion.
func (d *dumpState) dumpSlice(v reflect.Value) {
	// Determine whether this type should be hex dumped or not.  Also,
	// for types which should be hexdumped, try to use the underlying data
	// first, then fall back to trying to convert them to a uint8 slice.
	var buf []uint8
	doConvert := false
	doHexDump := false
	numEntries := v.Len()
	if numEntries > 0 {
		vt := v.Index(0).Type()
		vts := vt.String()
		switch {
		// C types that need to be converted.
		case cCharRE.MatchString(vts):
			fallthrough
		case cUnsignedCharRE.MatchString(vts):
			fallthrough
		case cUint8tCharRE.MatchString(vts):
			doConvert = true

		// Try to use existing uint8 slices and fall back to converting
		// and copying if that fails.
		case vt.Kind() == reflect.Uint8:
			// We need an addressable interface to convert the type
			// to a byte slice.  However, the reflect package won't
			// give us an interface on certain things like
			// unexported struct fields in order to enforce
			// visibility rules.  We use unsafe, when available, to
			// bypass these restrictions since this package does not
			// mutate the values.
			vs := v
			if !vs.CanInterface() || !vs.CanAddr() {
				vs = unsafeReflectValue(vs)
			}
			if !UnsafeDisabled {
				vs = vs.Slice(0, numEntries)

				// Use the existing uint8 slice if it can be
				// type asserted.
				iface := vs.Interface()
				if slice, ok := iface.([]uint8); ok {
					buf = slice
					doHexDump = true
					break
				}
			}

			// The underlying data needs to be converted if it can't
			// be type asserted to a uint8 slice.
			doConvert = true
		}

		// Copy and convert the underlying type if needed.
		if doConvert && vt.ConvertibleTo(uint8Type) {
			// Convert and copy each element into a uint8 byte
			// slice.
			buf = make([]uint8, numEntries)
			for i := 0; i < numEntries; i++ {
				vv := v.Index(i)
				buf[i] = uint8(vv.Convert(uint8Type).Uint())
			}
			doHexDump = true
		}
	}

	// Hexdump the entire slice as needed.
	if doHexDump && !d.cs.AsGolangSource {
		indent := strings.Repeat(d.cs.Indent, d.depth)
		str := indent + hex.Dump(buf)
		str = strings.Replace(str, "\n", "\n"+indent, -1)
		str = strings.TrimRight(str, d.cs.Indent)
		d.write([]byte(str))
		return
	}

	// Recursively call dump for each item.
	for i := 0; i < numEntries; i++ {
		d.dump(d.unpackValue(v.Index(i)))
		if i < (numEntries-1) || d.cs.AsGolangSource {
			d.write(commaNewlineBytes)
		} else {
			d.write(newlineBytes)
		}
	}
}

func isElementary(v reflect.Value) bool {
	switch v.Kind() {
	case reflect.Bool,
		reflect.Int,
		reflect.Int8,
		reflect.Int16,
		reflect.Int32,
		reflect.Int64,
		reflect.Uint,
		reflect.Uint8,
		reflect.Uint16,
		reflect.Uint32,
		reflect.Uint64,
		reflect.Uintptr,
		reflect.Float32,
		reflect.Float64,
		reflect.Complex64,
		reflect.Complex128,
		reflect.String:
		return true
	}
	return false
}

func isNil(v reflect.Value) bool {
	switch v.Kind() {
	case reflect.Chan,
		reflect.Func,
		reflect.Map,
		reflect.Ptr,
		reflect.UnsafePointer,
		reflect.Interface,
		reflect.Slice:
		return v.IsNil()
	}
	return false
}

func isInlineInitializable(v reflect.Value) bool {
	switch v.Kind() {
	case reflect.Bool,
		reflect.String:
		return false
	}
	return true
}

func (d *dumpState) write(b []byte) {
	if d.cs.AsGolangSource && d.pointerAccrual {
		return
	}
	d.w.Write(b)
}

// dump is the main workhorse for dumping a value.  It uses the passed reflect
// value to figure out what kind of object we are dealing with and formats it
// appropriately.  It is a recursive function, however circular data structures
// are detected and handled properly.
func (d *dumpState) dump(v reflect.Value) {
	// Handle invalid reflect values immediately.
	kind := v.Kind()
	if kind == reflect.Invalid {
		d.write(invalidAngleBytes)
		return
	}

	// Handle pointers specially.
	if kind == reflect.Ptr {
		d.indent()
		d.dumpPtr(v)
		return
	}

	// Print type information unless already handled elsewhere.
	if !d.ignoreNextType {
		if !d.cs.AsGolangSource {
			d.indent()
			d.write(openParenBytes)
			d.write([]byte(v.Type().String()))
			d.write(closeParenBytes)
			d.write(spaceBytes)
		} else {
			d.indent()
			// d.write(openParenBytes)
			if !isElementary(v) && !isNil(v) {
				d.write([]byte(v.Type().String()))
			}
			// d.write(closeParenBytes)
			d.write(spaceBytes)
		}
	}
	d.ignoreNextType = false

	// Display length and capacity if the built-in len and cap functions
	// work with the value's kind and the len/cap itself is non-zero.
	valueLen, valueCap := 0, 0
	switch v.Kind() {
	case reflect.Array, reflect.Slice, reflect.Chan:
		valueLen, valueCap = v.Len(), v.Cap()
	case reflect.Map, reflect.String:
		valueLen = v.Len()
	}
	if !d.cs.AsGolangSource && (valueLen != 0 || !d.cs.DisableCapacities && valueCap != 0) {
		d.write(openParenBytes)
		if valueLen != 0 {
			d.write(lenEqualsBytes)
			printInt(d.w, int64(valueLen), 10)
		}
		if !d.cs.DisableCapacities && valueCap != 0 {
			if valueLen != 0 {
				d.write(spaceBytes)
			}
			d.write(capEqualsBytes)
			printInt(d.w, int64(valueCap), 10)
		}
		d.write(closeParenBytes)
		d.write(spaceBytes)
	}

	// Call Stringer/error interfaces if they exist and the handle methods flag
	// is enabled
	if !d.cs.DisableMethods {
		if (kind != reflect.Invalid) && (kind != reflect.Interface) {
			if handled := handleMethods(d.cs, d.w, v); handled {
				return
			}
		}
	}

	switch kind {
	case reflect.Invalid:
		// Do nothing.  We should never get here since invalid has already
		// been handled above.

	case reflect.Bool:
		var b bytes.Buffer
		printBool(&b, v.Bool())
		d.write(b.Bytes())

	case reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64, reflect.Int:
		var b bytes.Buffer
		printInt(&b, v.Int(), 10)
		d.write(b.Bytes())

	case reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uint:
		var b bytes.Buffer
		printUint(&b, v.Uint(), 10)
		d.write(b.Bytes())

	case reflect.Float32:
		var b bytes.Buffer
		printFloat(&b, v.Float(), 32)
		d.write(b.Bytes())

	case reflect.Float64:
		var b bytes.Buffer
		printFloat(&b, v.Float(), 64)
		d.write(b.Bytes())

	case reflect.Complex64:
		var b bytes.Buffer
		printComplex(&b, v.Complex(), 32)
		d.write(b.Bytes())

	case reflect.Complex128:
		var b bytes.Buffer
		printComplex(&b, v.Complex(), 64)
		d.write(b.Bytes())

	case reflect.Slice:
		if v.IsNil() {
			d.write(d.cs.GetNilBytes())
			break
		}
		fallthrough

	case reflect.Array:
		d.write(openBraceNewlineBytes)
		d.depth++
		if (d.cs.MaxDepth != 0) && (d.depth > d.cs.MaxDepth) {
			d.indent()
			d.write(maxNewlineBytes)
		} else {
			d.dumpSlice(v)
		}
		d.depth--
		d.indent()
		d.write(closeBraceBytes)

	case reflect.String:
		d.write([]byte(strconv.Quote(v.String())))

	case reflect.Interface:
		// The only time we should get here is for nil interfaces due to
		// unpackValue calls.
		if v.IsNil() {
			d.write(d.cs.GetNilBytes())
		}

	case reflect.Ptr:
		// Do nothing.  We should never get here since pointers have already
		// been handled above.

	case reflect.Map:
		// nil maps should be indicated as different than empty maps
		if v.IsNil() {
			d.write(d.cs.GetNilBytes())
			break
		}

		d.write(openBraceNewlineBytes)
		d.depth++
		if (d.cs.MaxDepth != 0) && (d.depth > d.cs.MaxDepth) {
			d.indent()
			d.write(maxNewlineBytes)
		} else {
			numEntries := v.Len()
			keys := v.MapKeys()
			if d.cs.SortKeys {
				sortValues(keys, d.cs)
			}
			for i, key := range keys {
				d.dump(d.unpackValue(key))
				d.write(colonSpaceBytes)
				d.ignoreNextIndent = true
				d.dump(d.unpackValue(v.MapIndex(key)))
				if i < (numEntries-1) || d.cs.AsGolangSource {
					d.write(commaNewlineBytes)
				} else {
					d.write(newlineBytes)
				}
			}
		}
		d.depth--
		d.indent()
		d.write(closeBraceBytes)

	case reflect.Struct:
		d.write(openBraceNewlineBytes)
		d.depth++
		if (d.cs.MaxDepth != 0) && (d.depth > d.cs.MaxDepth) {
			d.indent()
			d.write(maxNewlineBytes)
		} else {
			vt := v.Type()
			numFields := v.NumField()
			for i := 0; i < numFields; i++ {
				vtf := vt.Field(i)
				if len(vtf.Name) > 0 && strings.ToLower(string(vtf.Name[0])) == string(vtf.Name[0]) && d.cs.AsGolangSource {
					continue
				}
				d.indent()
				d.write([]byte(vtf.Name))
				d.write(colonSpaceBytes)
				d.ignoreNextIndent = true
				d.dump(d.unpackValue(v.Field(i)))
				if i < (numFields-1) || d.cs.AsGolangSource {
					d.write(commaNewlineBytes)
				} else {
					d.write(newlineBytes)
				}
			}
		}
		d.depth--
		d.indent()
		d.write(closeBraceBytes)

	case reflect.Uintptr:
		var b bytes.Buffer
		d.cs.PrintHexPtr(&b, uintptr(v.Uint()))
		d.write(b.Bytes())

	case reflect.UnsafePointer, reflect.Chan, reflect.Func:
		var b bytes.Buffer
		d.cs.PrintHexPtr(&b, v.Pointer())
		d.write(b.Bytes())

	// There were not any other types at the time this code was written, but
	// fall back to letting the default fmt package handle it in case any new
	// types are added.
	default:
		if v.CanInterface() {
			var b bytes.Buffer
			fmt.Fprintf(&b, "%v", v.Interface())
			d.write(b.Bytes())
		} else {
			var b bytes.Buffer
			fmt.Fprintf(&b, "%v", v.String())
			d.write(b.Bytes())
		}
	}
}

// fdump is a helper function to consolidate the logic from the various public
// methods which take varying writers and config states.
func fdump(cs *ConfigState, w io.Writer, a ...interface{}) {
	for _, arg := range a {
		if arg == nil {
			w.Write(interfaceBytes)
			w.Write(spaceBytes)
			w.Write(cs.GetNilBytes())
			w.Write(newlineBytes)
			continue
		}

		d := dumpState{w: w, cs: cs}
		d.pointers = make(map[uintptr]int)
		d.pointerDefs = make(map[uintptr]reflect.Value)
		d.dump(reflect.ValueOf(arg))
		d.referenceFilling = true
		if cs.AsGolangSource {
			d.write(newlineBytes)
			for k, v := range d.pointerDefs {
				d.write(newlineBytes)
				d.write([]byte(fmt.Sprintf("var %s %s = &", d.generatePointerVarName(k), v.Type().String())))
				d.dumpPtr(v)
				d.write(newlineBytes)
			}
		}
		d.write(newlineBytes)
	}
}

// Fdump formats and displays the passed arguments to io.Writer w.  It formats
// exactly the same as Dump.
func Fdump(w io.Writer, a ...interface{}) {
	fdump(&Config, w, a...)
}

// Sdump returns a string with the passed arguments formatted exactly the same
// as Dump.
func Sdump(a ...interface{}) string {
	var buf bytes.Buffer
	fdump(&Config, &buf, a...)
	return buf.String()
}

/*
 Dump displays the passed parameters to standard out with newlines, customizable
 indentation, and additional debug information such as complete types and all
 pointer addresses used to indirect to the final value.  It provides the
 following features over the built-in printing facilities provided by the fmt
 package:

	 * Pointers are dereferenced and followed
	 * Circular data structures are detected and handled properly
	 * Custom Stringer/error interfaces are optionally invoked, including
		 on unexported types
	 * Custom types which only implement the Stringer/error interfaces via
		 a pointer receiver are optionally invoked when passing non-pointer
		 variables
	 * Byte arrays and slices are dumped like the hexdump -C command which
		 includes offsets, byte values in hex, and ASCII output

 The configuration options are controlled by an exported package global,
 spew.Config.  See ConfigState for options documentation.

 See Fdump if you would prefer dumping to an arbitrary io.Writer or Sdump to
 get the formatted result as a string.
*/
func Dump(a ...interface{}) {
	fdump(&Config, os.Stdout, a...)
}
