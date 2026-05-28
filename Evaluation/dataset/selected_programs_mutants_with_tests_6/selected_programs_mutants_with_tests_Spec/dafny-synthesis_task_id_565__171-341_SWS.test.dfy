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
var r0 := SplitStringIntoChars("a\0");
expect |r0| == |"a\0"|;
expect forall i: int {:trigger "a\0"[i]} {:trigger r0[i]} :: 0 <= i < |"a\0"| ==> r0[i] == "a\0"[i];
}
method {:test} Test2() {
var r0 := SplitStringIntoChars("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect |r0| == |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|;
expect forall i: int {:trigger "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i]} {:trigger r0[i]} :: 0 <= i < |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| ==> r0[i] == "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i];
}
method {:test} Test3() {
var r0 := SplitStringIntoChars("\U{0002}\0");
expect |r0| == |"\U{0002}\0"|;
expect forall i: int {:trigger "\U{0002}\0"[i]} {:trigger r0[i]} :: 0 <= i < |"\U{0002}\0"| ==> r0[i] == "\U{0002}\0"[i];
}
method {:test} Test4() {
var r0 := SplitStringIntoChars("\U{0002}\0a");
expect |r0| == |"\U{0002}\0a"|;
expect forall i: int {:trigger "\U{0002}\0a"[i]} {:trigger r0[i]} :: 0 <= i < |"\U{0002}\0a"| ==> r0[i] == "\U{0002}\0a"[i];
}
method {:test} Test5() {
var r0 := SplitStringIntoChars("\U{0002}\0");
expect |r0| == |"\U{0002}\0"|;
expect forall i: int {:trigger "\U{0002}\0"[i]} {:trigger r0[i]} :: 0 <= i < |"\U{0002}\0"| ==> r0[i] == "\U{0002}\0"[i];
}
