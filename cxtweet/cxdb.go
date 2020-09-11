// +build cxtweet

package cxtweet

import (
	"errors"
	"time"

	. "github.com/SkycoinProject/cx/cx"
	"github.com/boltdb/bolt"
)

type CXDB struct {
	b *bolt.DB
}

var cxdb *CXDB

func CXDBOpen() {
	cxdb = new(CXDB)
	b_, err := bolt.Open("cxdb.db", 0644, &bolt.Options{
		Timeout: time.Millisecond * 5000,
	})

	cxdb.b = b_

	if err != nil {
		panic("CXDB: cannot open!")
	}
}

func newBucket(prgm *CXProgram) {
	if cxdb == nil || cxdb.b == nil {
		CXDBOpen()
	}

	expr := prgm.GetExpr()
	fp := prgm.GetFramePointer()

	buckname := ReadStr(fp, expr.Inputs[0])

	err := cxdb.b.Update(func(tx *bolt.Tx) (err error) {
		_, err = tx.CreateBucketIfNotExists([]byte(buckname))
		return
	})

	WriteBool(GetFinalOffset(fp, expr.Outputs[0]), err == nil)
}

func strFetch(prgm *CXProgram) {
	if cxdb == nil || cxdb.b == nil {
		CXDBOpen()
	}

	expr := prgm.GetExpr()
	fp := prgm.GetFramePointer()

	buckname := []byte(ReadStr(fp, expr.Inputs[0]))
	query := []byte(ReadStr(fp, expr.Inputs[1]))

	//debug stuff
	//fmt.Printf(string(buckname) + " " + string(query) + "\n")

	_ = cxdb.b.View(func(tx *bolt.Tx) (err error) {
		wbkt := tx.Bucket(buckname)
		if wbkt != nil {
			val := wbkt.Get(query)
			if val != nil {
				outputSlicePointer := GetFinalOffset(fp, expr.Outputs[0])
				outputSliceOffset := GetPointerOffset(int32(outputSlicePointer))
				outputSliceOffset = int32(SliceResizeEx(outputSliceOffset, int32(len(val)), 1))
				copy(GetSliceData(outputSliceOffset, 1), val)
				WriteI32(outputSlicePointer, outputSliceOffset)
			} else {
				WriteI32(GetFinalOffset(fp, expr.Outputs[0]), int32(0))
			}
		} else {
			WriteI32(GetFinalOffset(fp, expr.Outputs[0]), int32(0))
		}
		return
	})
}

func strStore(prgm *CXProgram) {
	if cxdb == nil || cxdb.b == nil {
		CXDBOpen()
	}

	expr := prgm.GetExpr()
	fp := prgm.GetFramePointer()

	buckname := []byte(ReadStr(fp, expr.Inputs[0]))
	key := []byte(ReadStr(fp, expr.Inputs[1]))
	val := GetSliceData(GetSliceOffset(fp, expr.Inputs[2]), 1)

	//debug stuff
	//fmt.Printf(string(buckname) + " " + string(key) + ":" + string(val) + "\n")

	err := cxdb.b.Update(func(tx *bolt.Tx) (err error) {
		wbkt := tx.Bucket(buckname)
		if wbkt == nil {
			return errors.New("dummy")
		}

		err = wbkt.Put(key, val)
		return
	})

	WriteBool(GetFinalOffset(fp, expr.Outputs[0]), err == nil)
}

func walFetch(prgm *CXProgram) {
	if cxdb == nil || cxdb.b == nil {
		CXDBOpen()
	}

	expr := prgm.GetExpr()
	fp := prgm.GetFramePointer()

	buckname := []byte(ReadStr(fp, expr.Inputs[0]))
	query := ReadMemory(GetFinalOffset(fp, expr.Inputs[1]), expr.Inputs[1])

	_ = cxdb.b.View(func(tx *bolt.Tx) (err error) {
		wbkt := tx.Bucket(buckname)
		if wbkt != nil {
			val := wbkt.Get(query)
			if val != nil {
				outputSlicePointer := GetFinalOffset(fp, expr.Outputs[0])
				outputSliceOffset := GetPointerOffset(int32(outputSlicePointer))
				outputSliceOffset = int32(SliceResizeEx(outputSliceOffset, int32(len(val)), 1))
				copy(GetSliceData(outputSliceOffset, 1), val)
				WriteI32(outputSlicePointer, outputSliceOffset)
			} else {
				WriteI32(GetFinalOffset(fp, expr.Outputs[0]), int32(0))
			}
		} else {
			WriteI32(GetFinalOffset(fp, expr.Outputs[0]), int32(0))
		}
		return
	})
}

func walStore(prgm *CXProgram) {
	if cxdb == nil || cxdb.b == nil {
		CXDBOpen()
	}

	expr := prgm.GetExpr()
	fp := prgm.GetFramePointer()

	buckname := []byte(ReadStr(fp, expr.Inputs[0]))
	key := ReadMemory(GetFinalOffset(fp, expr.Inputs[1]), expr.Inputs[1])
	val := GetSliceData(GetSliceOffset(fp, expr.Inputs[2]), 1)

	err := cxdb.b.Update(func(tx *bolt.Tx) (err error) {
		wbkt := tx.Bucket(buckname)
		if wbkt == nil {
			return errors.New("dummy")
		}

		err = wbkt.Put(key, val)
		return
	})

	WriteBool(GetFinalOffset(fp, expr.Outputs[0]), err == nil)
}

func shaFetch(prgm *CXProgram) {
	if cxdb == nil || cxdb.b == nil {
		CXDBOpen()
	}

	expr := prgm.GetExpr()
	fp := prgm.GetFramePointer()

	buckname := []byte(ReadStr(fp, expr.Inputs[0]))
	query := ReadMemory(GetFinalOffset(fp, expr.Inputs[1]), expr.Inputs[1])

	_ = cxdb.b.View(func(tx *bolt.Tx) (err error) {
		wbkt := tx.Bucket(buckname)
		if wbkt != nil {
			val := wbkt.Get(query)
			if val != nil {
				outputSlicePointer := GetFinalOffset(fp, expr.Outputs[0])
				outputSliceOffset := GetPointerOffset(int32(outputSlicePointer))
				outputSliceOffset = int32(SliceResizeEx(outputSliceOffset, int32(len(val)), 1))
				copy(GetSliceData(outputSliceOffset, 1), val)
				WriteI32(outputSlicePointer, outputSliceOffset)
			} else {
				WriteI32(GetFinalOffset(fp, expr.Outputs[0]), int32(0))
			}
		} else {
			WriteI32(GetFinalOffset(fp, expr.Outputs[0]), int32(0))
		}
		return
	})
}

func shaStore(prgm *CXProgram) {
	if cxdb == nil || cxdb.b == nil {
		CXDBOpen()
	}

	expr := prgm.GetExpr()
	fp := prgm.GetFramePointer()

	buckname := []byte(ReadStr(fp, expr.Inputs[0]))
	key := ReadMemory(GetFinalOffset(fp, expr.Inputs[1]), expr.Inputs[1])
	val := GetSliceData(GetSliceOffset(fp, expr.Inputs[2]), 1)

	err := cxdb.b.Update(func(tx *bolt.Tx) (err error) {
		wbkt := tx.Bucket(buckname)
		if wbkt == nil {
			return errors.New("dummy")
		}

		err = wbkt.Put(key, val)
		return
	})

	WriteBool(GetFinalOffset(fp, expr.Outputs[0]), err == nil)
}
