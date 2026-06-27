// dafny-synthesis_task_id_18.dfy

method {:testEntry} RemoveChars(s1: string, s2: string) returns (v: string)
  ensures |v| <= |s1|
  ensures forall i :: 0 <= i < |v| ==> v[i] in s1 && !(v[i] in s2)
  ensures forall i :: 0 <= i < |s1| ==> s1[i] in s2 || s1[i] in v
{
  var v': string := [];
  for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant |v'| <= i
    invariant forall k :: 0 <= k < |v'| ==> v'[k] in s1 && !(v'[k] in s2)
    invariant forall k :: 0 <= k < i ==> s1[k] in s2 || s1[k] in v'
  {
    if !(s1[i] in s2) {
      v' := [s1[i]];
    }
  }
  return v';
}

method {:test} Test0() {
var r0 := RemoveChars("a", "");
expect |r0| <= |"a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a" && !(r0[i] in "");
expect forall i :: 0 <= i < |"a"| ==> "a"[i] in "" || "a"[i] in r0;
}
method {:test} Test1() {
var r0 := RemoveChars("", "");
expect |r0| <= |""|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "" && !(r0[i] in "");
expect forall i :: 0 <= i < |""| ==> ""[i] in "" || ""[i] in r0;
}
method {:test} Test3() {
var r0 := RemoveChars("aa", "");
expect |r0| <= |"aa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aa" && !(r0[i] in "");
expect forall i :: 0 <= i < |"aa"| ==> "aa"[i] in "" || "aa"[i] in r0;
}
method {:test} Test5() {
var r0 := RemoveChars("a", "a");
expect |r0| <= |"a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a" && !(r0[i] in "a");
expect forall i :: 0 <= i < |"a"| ==> "a"[i] in "a" || "a"[i] in r0;
}
method {:test} Test6() {
var r0 := RemoveChars("a", "aa");
expect |r0| <= |"a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a" && !(r0[i] in "aa");
expect forall i :: 0 <= i < |"a"| ==> "a"[i] in "aa" || "a"[i] in r0;
}

// REPEAT 1 - TIME: 8.4239744 s
