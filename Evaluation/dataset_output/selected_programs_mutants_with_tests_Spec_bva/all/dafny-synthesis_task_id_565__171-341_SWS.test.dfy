// dafny-synthesis_task_id_565.dfy

method {:testEntry} SplitStringIntoChars(s: string) returns (v: seq<char>)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> v[i] == s[i]
{
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |v| == i
    invariant forall k :: 0 <= k < i ==> v[k] == s[k]
  {
    v := v + [s[i]];
  }
  v := [];
}


method {:test} Test0() {
var r0 := SplitStringIntoChars("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> r0[i] == "a"[i];
}
method {:test} Test1() {
var r0 := SplitStringIntoChars("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> r0[i] == ""[i];
}
method {:test} Test3() {
var r0 := SplitStringIntoChars("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> r0[i] == "aa"[i];
}

// REPEAT 1 - TIME: 9.1116289 s

method {:test} Test10() {
var r0 := SplitStringIntoChars("\U{0002}\0");
expect |r0| == |"\U{0002}\0"|;
expect forall i :: 0 <= i < |"\U{0002}\0"| ==> r0[i] == "\U{0002}\0"[i];
}

// REPEAT 2 - TIME: 10.2091725 s

method {:test} Test11() {
var r0 := SplitStringIntoChars("a\0\U{0002}");
expect |r0| == |"a\0\U{0002}"|;
expect forall i :: 0 <= i < |"a\0\U{0002}"| ==> r0[i] == "a\0\U{0002}"[i];
}

// REPEAT 3 - TIME: 11.3102981 s

method {:test} Test12() {
var r0 := SplitStringIntoChars("\0aa");
expect |r0| == |"\0aa"|;
expect forall i :: 0 <= i < |"\0aa"| ==> r0[i] == "\0aa"[i];
}

// REPEAT 4 - TIME: 12.3790933 s

method {:test} Test13() {
var r0 := SplitStringIntoChars("a\U{0002}\U{0004}\0");
expect |r0| == |"a\U{0002}\U{0004}\0"|;
expect forall i :: 0 <= i < |"a\U{0002}\U{0004}\0"| ==> r0[i] == "a\U{0002}\U{0004}\0"[i];
}

// REPEAT 5 - TIME: 13.6444586 s

method {:test} Test14() {
var r0 := SplitStringIntoChars("aaa\U{0002}\0aaaaaaaaaaaaaaaaaaaaa\U{0004}");
expect |r0| == |"aaa\U{0002}\0aaaaaaaaaaaaaaaaaaaaa\U{0004}"|;
expect forall i :: 0 <= i < |"aaa\U{0002}\0aaaaaaaaaaaaaaaaaaaaa\U{0004}"| ==> r0[i] == "aaa\U{0002}\0aaaaaaaaaaaaaaaaaaaaa\U{0004}"[i];
}

// REPEAT 6 - TIME: 14.7323274 s

method {:test} Test15() {
var r0 := SplitStringIntoChars("\U{0006}\0\U{0004}\U{0002}");
expect |r0| == |"\U{0006}\0\U{0004}\U{0002}"|;
expect forall i :: 0 <= i < |"\U{0006}\0\U{0004}\U{0002}"| ==> r0[i] == "\U{0006}\0\U{0004}\U{0002}"[i];
}

// REPEAT 7 - TIME: 15.586976 s

method {:test} Test16() {
var r0 := SplitStringIntoChars("\0aaa\U{0002}");
expect |r0| == |"\0aaa\U{0002}"|;
expect forall i :: 0 <= i < |"\0aaa\U{0002}"| ==> r0[i] == "\0aaa\U{0002}"[i];
}

// REPEAT 8 - TIME: 16.3499487 s

method {:test} Test17() {
var r0 := SplitStringIntoChars("\U{0004}\0aa\U{0002}");
expect |r0| == |"\U{0004}\0aa\U{0002}"|;
expect forall i :: 0 <= i < |"\U{0004}\0aa\U{0002}"| ==> r0[i] == "\U{0004}\0aa\U{0002}"[i];
}

// REPEAT 9 - TIME: 17.1780689 s

method {:test} Test18() {
var r0 := SplitStringIntoChars("\U{0006}\U{0002}aa\0\U{0004}");
expect |r0| == |"\U{0006}\U{0002}aa\0\U{0004}"|;
expect forall i :: 0 <= i < |"\U{0006}\U{0002}aa\0\U{0004}"| ==> r0[i] == "\U{0006}\U{0002}aa\0\U{0004}"[i];
}

// REPEAT 10 - TIME: 18.016868 s
