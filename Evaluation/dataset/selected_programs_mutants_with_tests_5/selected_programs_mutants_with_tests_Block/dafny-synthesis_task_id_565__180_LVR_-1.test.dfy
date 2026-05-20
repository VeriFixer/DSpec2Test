// dafny-synthesis_task_id_565.dfy

method {:testEntry} SplitStringIntoChars(s: string) returns (v: seq<char>)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> v[i] == s[i]
{
  v := [];
  for i := -1 to |s|
    invariant 0 <= i <= |s|
    invariant |v| == i
    invariant forall k :: 0 <= k < i ==> v[k] == s[k]
  {
    v := v + [s[i]];
  }
}

method {:test} Test0() {
var r0 := SplitStringIntoChars("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[i];
}
method {:test} Test1() {
var r0 := SplitStringIntoChars("\0a");
expect |r0| == |"\0a"|;
expect forall i: int {:trigger "\0a"[i]} {:trigger r0[i]} :: 0 <= i < |"\0a"| ==> r0[i] == "\0a"[i];
}
method {:test} Test2() {
var r0 := SplitStringIntoChars("\0aa");
expect |r0| == |"\0aa"|;
expect forall i: int {:trigger "\0aa"[i]} {:trigger r0[i]} :: 0 <= i < |"\0aa"| ==> r0[i] == "\0aa"[i];
}
method {:test} Test3() {
var r0 := SplitStringIntoChars("\0aaa");
expect |r0| == |"\0aaa"|;
expect forall i: int {:trigger "\0aaa"[i]} {:trigger r0[i]} :: 0 <= i < |"\0aaa"| ==> r0[i] == "\0aaa"[i];
}
method {:test} Test4() {
var r0 := SplitStringIntoChars("\0\U{0002}aa\U{0004}");
expect |r0| == |"\0\U{0002}aa\U{0004}"|;
expect forall i: int {:trigger "\0\U{0002}aa\U{0004}"[i]} {:trigger r0[i]} :: 0 <= i < |"\0\U{0002}aa\U{0004}"| ==> r0[i] == "\0\U{0002}aa\U{0004}"[i];
}
