// dafny-synthesis_task_id_565.dfy

method {:testEntry} SplitStringIntoChars(s: string) returns (v: seq<char>)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> v[i] == s[i]
{
  v := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |v| == i
    invariant forall k :: 0 <= k < i ==> v[k] == s[k]
  {
    v := v;
  }
}


method {:test} Test0() {
var r0 := SplitStringIntoChars("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> r0[i] == "a"[i];
}

// REPEAT 1 - TIME: 2.7963975 s

method {:test} Test1() {
var r0 := SplitStringIntoChars("a\0");
expect |r0| == |"a\0"|;
expect forall i :: 0 <= i < |"a\0"| ==> r0[i] == "a\0"[i];
}

// REPEAT 2 - TIME: 3.7318458 s

method {:test} Test2() {
var r0 := SplitStringIntoChars("a\0aaaaaaaaaa\U{0002}");
expect |r0| == |"a\0aaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |"a\0aaaaaaaaaa\U{0002}"| ==> r0[i] == "a\0aaaaaaaaaa\U{0002}"[i];
}

// REPEAT 3 - TIME: 4.6450307 s

method {:test} Test3() {
var r0 := SplitStringIntoChars("\U{0002}\U{0004}\0");
expect |r0| == |"\U{0002}\U{0004}\0"|;
expect forall i :: 0 <= i < |"\U{0002}\U{0004}\0"| ==> r0[i] == "\U{0002}\U{0004}\0"[i];
}

// REPEAT 4 - TIME: 5.6588652 s

method {:test} Test4() {
var r0 := SplitStringIntoChars("\U{0004}\0\U{0002}a");
expect |r0| == |"\U{0004}\0\U{0002}a"|;
expect forall i :: 0 <= i < |"\U{0004}\0\U{0002}a"| ==> r0[i] == "\U{0004}\0\U{0002}a"[i];
}

// REPEAT 5 - TIME: 6.6620217 s

method {:test} Test5() {
var r0 := SplitStringIntoChars("\0aaaaaaaaaaaaa\U{0002}");
expect |r0| == |"\0aaaaaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |"\0aaaaaaaaaaaaa\U{0002}"| ==> r0[i] == "\0aaaaaaaaaaaaa\U{0002}"[i];
}

// REPEAT 6 - TIME: 7.6080379 s

method {:test} Test6() {
var r0 := SplitStringIntoChars("\U{0002}\0");
expect |r0| == |"\U{0002}\0"|;
expect forall i :: 0 <= i < |"\U{0002}\0"| ==> r0[i] == "\U{0002}\0"[i];
}

// REPEAT 7 - TIME: 8.45073 s

method {:test} Test7() {
var r0 := SplitStringIntoChars("\U{0002}\0aaaaaaaa\U{0004}");
expect |r0| == |"\U{0002}\0aaaaaaaa\U{0004}"|;
expect forall i :: 0 <= i < |"\U{0002}\0aaaaaaaa\U{0004}"| ==> r0[i] == "\U{0002}\0aaaaaaaa\U{0004}"[i];
}

// REPEAT 8 - TIME: 9.2160559 s

method {:test} Test8() {
var r0 := SplitStringIntoChars("\U{0002}\0aa");
expect |r0| == |"\U{0002}\0aa"|;
expect forall i :: 0 <= i < |"\U{0002}\0aa"| ==> r0[i] == "\U{0002}\0aa"[i];
}

// REPEAT 9 - TIME: 10.0672036 s

method {:test} Test9() {
var r0 := SplitStringIntoChars("\U{0004}\0\U{0002}");
expect |r0| == |"\U{0004}\0\U{0002}"|;
expect forall i :: 0 <= i < |"\U{0004}\0\U{0002}"| ==> r0[i] == "\U{0004}\0\U{0002}"[i];
}

// REPEAT 10 - TIME: 10.7833468 s
