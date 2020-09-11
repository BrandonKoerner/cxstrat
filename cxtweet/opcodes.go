// +build cxtweet

package cxtweet

import (
	. "github.com/SkycoinProject/cx/cx"
	. "github.com/SkycoinProject/cx/cx/base"
)

const (
	OP_CXTWEET_BEGIN = iota + END_OF_BASE_OPS + 1000

	//utility operations
	OP_CXTWEET_STR2BYTES
	OP_CXTWEET_BYTES2STR
	OP_CXTWEET_SUMSHA256
	OP_CXTWEET_RDADDRESS
	OP_CXTWEET_BTADDRESS

	//blockchain operations
	OP_CXTWEET_GETBLOCK
	OP_CXTWEET_CHAINLEN
	OP_CXTWEET_NEWTWEET
	OP_CXTWEET_NEWRETWT
	OP_CXTWEET_NEWLIKE
	OP_CXTWEET_LAUNCH
	OP_CXTWEET_CHGNAME
	OP_CXTWEET_MKACCOUNT

	//boltdb operations
	OP_CXTWEET_NEWBUCKET
	OP_CXTWEET_STRFETCH
	OP_CXTWEET_STRSTORE
	OP_CXTWEET_WALFETCH
	OP_CXTWEET_WALSTORE
	OP_CXTWEET_SHAFETCH
	OP_CXTWEET_SHASTORE

	OP_CXTWEET_STALL
	OP_CXTWEET_EXPOSE
	OP_CXTWEET_LAUNCHAPI

	END_OF_CXTWEET_OPS
)

func init() {
	Op(OP_CXTWEET_STR2BYTES, "cxtweet.str2bytes", str2Bytes, In(ASTR), Out(Slice(TYPE_UI8)))
	Op(OP_CXTWEET_BYTES2STR, "cxtweet.bytes2str", bytes2Str, In(Slice(TYPE_UI8)), Out(ASTR))
	Op(OP_CXTWEET_SUMSHA256, "cxtweet.sumsha256", sumSha256, In(Slice(TYPE_UI8)), Out(Array(TYPE_UI8, 32)))
	Op(OP_CXTWEET_RDADDRESS, "cxtweet.rdaddress", rdAddress, In(Array(TYPE_UI8, 25)), Out(ASTR))
	Op(OP_CXTWEET_BTADDRESS, "cxtweet.btaddress", btAddress, In(Slice(TYPE_UI8)), Out(Array(TYPE_UI8, 25)))

	Op(OP_CXTWEET_GETBLOCK, "cxtweet.getblock", getBlock, In(AI32), Out(Slice(TYPE_UI8)))
	Op(OP_CXTWEET_CHAINLEN, "cxtweet.chainlen", chainLen, nil, Out(AI32))
	Op(OP_CXTWEET_NEWTWEET, "cxtweet.newtweet", newTweet, In(Slice(TYPE_UI8)), Out(ABOOL))
	Op(OP_CXTWEET_NEWRETWT, "cxtweet.newretweet", newRetweet, In(Array(TYPE_UI8, 32)), Out(ABOOL))
	Op(OP_CXTWEET_NEWLIKE, "cxtweet.newlike", newLike, In(Array(TYPE_UI8, 32)), Out(ABOOL))
	Op(OP_CXTWEET_LAUNCH, "cxtweet.launch", launchCXTweet, nil, Out(ABOOL))
	Op(OP_CXTWEET_CHGNAME, "cxtweet.chgname", changeName, In(ASTR), Out(ABOOL))
	Op(OP_CXTWEET_MKACCOUNT, "cxtweet.mkaccount", makeAccount, nil, Out(ABOOL))

	Op(OP_CXTWEET_NEWBUCKET, "cxtweet.newbucket", newBucket, In(ASTR), Out(ABOOL))
	Op(OP_CXTWEET_STRFETCH, "cxtweet.strfetch", strFetch, In(ASTR, ASTR), Out(Slice(TYPE_UI8)))
	Op(OP_CXTWEET_STRSTORE, "cxtweet.strstore", strStore, In(ASTR, ASTR, Slice(TYPE_UI8)), Out(ABOOL))
	Op(OP_CXTWEET_WALFETCH, "cxtweet.walfetch", walFetch, In(ASTR, Array(TYPE_UI8, 25)), Out(Slice(TYPE_UI8)))
	Op(OP_CXTWEET_WALSTORE, "cxtweet.walstore", walStore, In(ASTR, Array(TYPE_UI8, 25), Slice(TYPE_UI8)), Out(ABOOL))
	Op(OP_CXTWEET_SHAFETCH, "cxtweet.shafetch", shaFetch, In(ASTR, Array(TYPE_UI8, 32)), Out(Slice(TYPE_UI8)))
	Op(OP_CXTWEET_SHASTORE, "cxtweet.shastore", shaStore, In(ASTR, Array(TYPE_UI8, 32), Slice(TYPE_UI8)), Out(ABOOL))

	Op(OP_CXTWEET_STALL, "cxtweet.stall", stall, nil, Out(Slice(TYPE_UI8)))
	Op(OP_CXTWEET_EXPOSE, "cxtweet.expose", expose, In(Slice(TYPE_UI8)), nil)
	Op(OP_CXTWEET_LAUNCHAPI, "cxtweet.launchapi", launchApi, nil, Out(ABOOL))
}
