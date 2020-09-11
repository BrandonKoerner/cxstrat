// +build cxtweet

package cxtweet

import (
	. "github.com/SkycoinProject/cx/cx"
	"github.com/SkycoinProject/skycoin/src/cipher"
)

func str2Bytes(prgm *CXProgram) {
	expr := prgm.GetExpr()
	fp := prgm.GetFramePointer()

	input1, output1 := expr.Inputs[0], expr.Outputs[0]

	byts := []byte(ReadStr(fp, input1))
	outputSlicePointer := GetFinalOffset(fp, output1)
	outputSliceOffset := GetPointerOffset(int32(outputSlicePointer))
	outputSliceOffset = int32(SliceResizeEx(outputSliceOffset, int32(len(byts)), 1))
	copy(GetSliceData(outputSliceOffset, 1), byts)
	WriteI32(outputSlicePointer, outputSliceOffset)
}

func bytes2Str(prgm *CXProgram) {
	expr := prgm.GetExpr()
	fp := prgm.GetFramePointer()

	inputSliceOffset := GetSliceOffset(fp, expr.Inputs[0])
	byts := GetSliceData(inputSliceOffset, 1)

	str := string(byts)
	//fmt.Println(str)
	WriteString(fp, str, expr.Outputs[0])
}

func sumSha256(prgm *CXProgram) {
	//expects ui8 slice, returns [32]ui8 hash.
	expr := prgm.GetExpr()
	fp := prgm.GetFramePointer()

	inputSliceOffset := GetSliceOffset(fp, expr.Inputs[0])
	byts := GetSliceData(inputSliceOffset, 1)
	hsh := cipher.SumSHA256(byts)

	WriteMemory(GetFinalOffset(fp, expr.Outputs[0]), hsh[:])
}

func rdAddress(prgm *CXProgram) {
	//expects ui8 slice, returns [32]ui8 hash.
	expr := prgm.GetExpr()
	fp := prgm.GetFramePointer()

	abyts := ReadMemory(GetFinalOffset(fp, expr.Inputs[0]), expr.Inputs[0])

	a, _ := cipher.AddressFromBytes(abyts)
	astr := a.String()

	WriteString(fp, astr, expr.Outputs[0])
}

func btAddress(prgm *CXProgram) {
	//expects ui8 slice, returns [32]ui8 hash.
	expr := prgm.GetExpr()
	fp := prgm.GetFramePointer()

	inputSliceOffset := GetSliceOffset(fp, expr.Inputs[0])
	byts := GetSliceData(inputSliceOffset, 1)

	abyts := string(byts)
	a, _ := cipher.DecodeBase58Address(abyts)
	astr := a.Bytes()

	WriteMemory(GetFinalOffset(fp, expr.Outputs[0]), astr)
}
