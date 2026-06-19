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
  }
}


method {:test} Test0() {
var r0 := SplitStringIntoChars("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> r0[i] == "a"[i];
}

// REPEAT 1 - TIME: 2.6360642 s

method {:test} Test1() {
var r0 := SplitStringIntoChars("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> r0[i] == "aa"[i];
}

// REPEAT 2 - TIME: 3.3939865 s

method {:test} Test2() {
var r0 := SplitStringIntoChars("aaa");
expect |r0| == |"aaa"|;
expect forall i :: 0 <= i < |"aaa"| ==> r0[i] == "aaa"[i];
}

// REPEAT 3 - TIME: 4.1136897 s

method {:test} Test3() {
var r0 := SplitStringIntoChars("\0aa");
expect |r0| == |"\0aa"|;
expect forall i :: 0 <= i < |"\0aa"| ==> r0[i] == "\0aa"[i];
}

// REPEAT 4 - TIME: 5.0501089 s

method {:test} Test4() {
var r0 := SplitStringIntoChars("\U{0002}\0");
expect |r0| == |"\U{0002}\0"|;
expect forall i :: 0 <= i < |"\U{0002}\0"| ==> r0[i] == "\U{0002}\0"[i];
}

// REPEAT 5 - TIME: 6.0124995 s

method {:test} Test5() {
var r0 := SplitStringIntoChars("\U{0002}\0a");
expect |r0| == |"\U{0002}\0a"|;
expect forall i :: 0 <= i < |"\U{0002}\0a"| ==> r0[i] == "\U{0002}\0a"[i];
}

// REPEAT 6 - TIME: 6.6853581 s

method {:test} Test6() {
var r0 := SplitStringIntoChars("\0aaa");
expect |r0| == |"\0aaa"|;
expect forall i :: 0 <= i < |"\0aaa"| ==> r0[i] == "\0aaa"[i];
}

// REPEAT 7 - TIME: 7.4780318 s

method {:test} Test7() {
var r0 := SplitStringIntoChars("\U{0002}\0aa");
expect |r0| == |"\U{0002}\0aa"|;
expect forall i :: 0 <= i < |"\U{0002}\0aa"| ==> r0[i] == "\U{0002}\0aa"[i];
}

// REPEAT 8 - TIME: 8.1985031 s

method {:test} Test8() {
var r0 := SplitStringIntoChars("\0aaaa");
expect |r0| == |"\0aaaa"|;
expect forall i :: 0 <= i < |"\0aaaa"| ==> r0[i] == "\0aaaa"[i];
}

// REPEAT 9 - TIME: 8.8627918 s

method {:test} Test9() {
var r0 := SplitStringIntoChars("\0aaa\U{0002}\U{0004}");
expect |r0| == |"\0aaa\U{0002}\U{0004}"|;
expect forall i :: 0 <= i < |"\0aaa\U{0002}\U{0004}"| ==> r0[i] == "\0aaa\U{0002}\U{0004}"[i];
}

// REPEAT 10 - TIME: 9.4883317 s
