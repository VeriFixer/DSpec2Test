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
    break;
    v := v + [s[i]];
  }
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

// REPEAT 1 - TIME: 6.7808989 s

method {:test} Test10() {
var r0 := SplitStringIntoChars("a\0a");
expect |r0| == |"a\0a"|;
expect forall i :: 0 <= i < |"a\0a"| ==> r0[i] == "a\0a"[i];
}

// REPEAT 2 - TIME: 7.6741041 s

method {:test} Test11() {
var r0 := SplitStringIntoChars("\U{0002}\0");
expect |r0| == |"\U{0002}\0"|;
expect forall i :: 0 <= i < |"\U{0002}\0"| ==> r0[i] == "\U{0002}\0"[i];
}

// REPEAT 3 - TIME: 8.3974009 s

method {:test} Test12() {
var r0 := SplitStringIntoChars("a\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect |r0| == |"a\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |"a\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| ==> r0[i] == "a\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i];
}

// REPEAT 4 - TIME: 9.1065298 s

method {:test} Test13() {
var r0 := SplitStringIntoChars("\0aaa");
expect |r0| == |"\0aaa"|;
expect forall i :: 0 <= i < |"\0aaa"| ==> r0[i] == "\0aaa"[i];
}

// REPEAT 5 - TIME: 9.7398065 s

method {:test} Test14() {
var r0 := SplitStringIntoChars("\U{0002}\0aa");
expect |r0| == |"\U{0002}\0aa"|;
expect forall i :: 0 <= i < |"\U{0002}\0aa"| ==> r0[i] == "\U{0002}\0aa"[i];
}

// REPEAT 6 - TIME: 10.4949003 s

method {:test} Test15() {
var r0 := SplitStringIntoChars("\U{0002}\0a");
expect |r0| == |"\U{0002}\0a"|;
expect forall i :: 0 <= i < |"\U{0002}\0a"| ==> r0[i] == "\U{0002}\0a"[i];
}

// REPEAT 7 - TIME: 11.1438275 s

method {:test} Test16() {
var r0 := SplitStringIntoChars("\U{0002}\0\U{0004}aa");
expect |r0| == |"\U{0002}\0\U{0004}aa"|;
expect forall i :: 0 <= i < |"\U{0002}\0\U{0004}aa"| ==> r0[i] == "\U{0002}\0\U{0004}aa"[i];
}

// REPEAT 8 - TIME: 11.7727754 s

method {:test} Test17() {
var r0 := SplitStringIntoChars("\U{0002}\0aaaa");
expect |r0| == |"\U{0002}\0aaaa"|;
expect forall i :: 0 <= i < |"\U{0002}\0aaaa"| ==> r0[i] == "\U{0002}\0aaaa"[i];
}

// REPEAT 9 - TIME: 12.5093145 s

method {:test} Test18() {
var r0 := SplitStringIntoChars("\U{0002}aaaa\n\U{000C}aaaaaa\0aa\U{0006}\U{0008}aaaaaaaa\U{0004}a\U{000E}");
expect |r0| == |"\U{0002}aaaa\n\U{000C}aaaaaa\0aa\U{0006}\U{0008}aaaaaaaa\U{0004}a\U{000E}"|;
expect forall i :: 0 <= i < |"\U{0002}aaaa\n\U{000C}aaaaaa\0aa\U{0006}\U{0008}aaaaaaaa\U{0004}a\U{000E}"| ==> r0[i] == "\U{0002}aaaa\n\U{000C}aaaaaa\0aa\U{0006}\U{0008}aaaaaaaa\U{0004}a\U{000E}"[i];
}

// REPEAT 10 - TIME: 13.2008767 s
