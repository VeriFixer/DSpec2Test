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
method {:test} Test10() {
var r0 := SplitStringIntoChars("\U{0002}\0");
expect |r0| == |"\U{0002}\0"|;
expect forall i: int {:trigger "\U{0002}\0"[i]} {:trigger r0[i]} :: 0 <= i < |"\U{0002}\0"| ==> r0[i] == "\U{0002}\0"[i];
}
method {:test} Test11() {
var r0 := SplitStringIntoChars("a\0\U{0002}");
expect |r0| == |"a\0\U{0002}"|;
expect forall i: int {:trigger "a\0\U{0002}"[i]} {:trigger r0[i]} :: 0 <= i < |"a\0\U{0002}"| ==> r0[i] == "a\0\U{0002}"[i];
}
method {:test} Test12() {
var r0 := SplitStringIntoChars("\0aa");
expect |r0| == |"\0aa"|;
expect forall i: int {:trigger "\0aa"[i]} {:trigger r0[i]} :: 0 <= i < |"\0aa"| ==> r0[i] == "\0aa"[i];
}
method {:test} Test13() {
var r0 := SplitStringIntoChars("a\U{0002}\U{0004}\0");
expect |r0| == |"a\U{0002}\U{0004}\0"|;
expect forall i: int {:trigger "a\U{0002}\U{0004}\0"[i]} {:trigger r0[i]} :: 0 <= i < |"a\U{0002}\U{0004}\0"| ==> r0[i] == "a\U{0002}\U{0004}\0"[i];
}
method {:test} Test14() {
var r0 := SplitStringIntoChars("aaa\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}");
expect |r0| == |"aaa\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"|;
expect forall i: int {:trigger "aaa\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"[i]} {:trigger r0[i]} :: 0 <= i < |"aaa\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"| ==> r0[i] == "aaa\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"[i];
}
method {:test} Test15() {
var r0 := SplitStringIntoChars("a\0aaaaaa\U{0006}aaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaa\U{0002}\U{0008}");
expect |r0| == |"a\0aaaaaa\U{0006}aaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaa\U{0002}\U{0008}"|;
expect forall i: int {:trigger "a\0aaaaaa\U{0006}aaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaa\U{0002}\U{0008}"[i]} {:trigger r0[i]} :: 0 <= i < |"a\0aaaaaa\U{0006}aaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaa\U{0002}\U{0008}"| ==> r0[i] == "a\0aaaaaa\U{0006}aaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaa\U{0002}\U{0008}"[i];
}
