
method {:test} Test18() {
var r0 := ReplaceWithColon("\U{0005}aaaaa\U{0002}a\U{0003}\U{0004}aaaaaaa\0aaa\U{0001}aaaaa");
expect |r0| == |"\U{0005}aaaaa\U{0002}a\U{0003}\U{0004}aaaaaaa\0aaa\U{0001}aaaaa"|;
expect forall i :: 0 <= i < |"\U{0005}aaaaa\U{0002}a\U{0003}\U{0004}aaaaaaa\0aaa\U{0001}aaaaa"| ==> (IsSpaceCommaDot("\U{0005}aaaaa\U{0002}a\U{0003}\U{0004}aaaaaaa\0aaa\U{0001}aaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\U{0005}aaaaa\U{0002}a\U{0003}\U{0004}aaaaaaa\0aaa\U{0001}aaaaa"[i]) ==> r0[i] == "\U{0005}aaaaa\U{0002}a\U{0003}\U{0004}aaaaaaa\0aaa\U{0001}aaaaa"[i]);
}

// REPEAT 10 - TIME: 12.2204044 s