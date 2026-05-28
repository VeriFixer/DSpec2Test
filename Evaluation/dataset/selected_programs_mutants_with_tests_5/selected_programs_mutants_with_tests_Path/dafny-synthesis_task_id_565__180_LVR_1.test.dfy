// dafny-synthesis_task_id_565.dfy

method {:testEntry} SplitStringIntoChars(s: string) returns (v: seq<char>)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> v[i] == s[i]
{
  v := [];
  for i := 1 to |s|
    invariant 0 <= i <= |s|
    invariant |v| == i
    invariant forall k :: 0 <= k < i ==> v[k] == s[k]
  {
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
expect forall i: int {:trigger ""[i]} {:trigger r0[i]} :: 0 <= i < |""| ==> r0[i] == ""[i];
}
method {:test} Test2() {
var r0 := SplitStringIntoChars("\0");
expect |r0| == |"\0"|;
expect forall i: int {:trigger "\0"[i]} {:trigger r0[i]} :: 0 <= i < |"\0"| ==> r0[i] == "\0"[i];
}
method {:test} Test3() {
var r0 := SplitStringIntoChars("aa");
expect |r0| == |"aa"|;
expect forall i: int {:trigger "aa"[i]} {:trigger r0[i]} :: 0 <= i < |"aa"| ==> r0[i] == "aa"[i];
}
method {:test} Test4() {
var r0 := SplitStringIntoChars("\0a");
expect |r0| == |"\0a"|;
expect forall i: int {:trigger "\0a"[i]} {:trigger r0[i]} :: 0 <= i < |"\0a"| ==> r0[i] == "\0a"[i];
}
