// dafny-synthesis_task_id_251.dfy

method {:testEntry} InsertBeforeEach(s: seq<string>, x: string) returns (v: seq<string>)
  ensures |v| == 2 * |s|
  ensures forall i :: 0 <= i < |s| ==> v[2 * i] == x && v[2 * i + 1] == s[i]
{
  v := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |v| == 2 * i
    invariant forall j :: 0 <= j < i ==> v[2 * j] == x && v[2 * j + 1] == s[j]
  {
    v := [x, s[i]];
  }
}


method {:test} Test0() {
var seqstring0 : seq<string> := [""];
var r0 := InsertBeforeEach(seqstring0, "");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 1 - TIME: 14.7546377 s

method {:test} Test1() {
var seqstring0 : seq<string> := ["", ""];
var r0 := InsertBeforeEach(seqstring0, "a");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "a" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 2 - TIME: 26.3247489 s

method {:test} Test2() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\0");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\0" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 3 - TIME: 37.9774623 s

method {:test} Test3() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "a\0");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "a\0" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 4 - TIME: 49.3605607 s

method {:test} Test4() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\0aaaaaaaaaaaaaaa\U{0002}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\0aaaaaaaaaaaaaaa\U{0002}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 5 - TIME: 59.7213794 s

method {:test} Test5() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0002}a\0");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0002}a\0" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 6 - TIME: 72.4952277 s

method {:test} Test6() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0002}\0a\U{0004}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0002}\0a\U{0004}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 7 - TIME: 84.9130571 s

method {:test} Test7() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\0");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\0" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 8 - TIME: 100.0802533 s

method {:test} Test8() {
var seqstring0 : seq<string> := ["", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0002}\0");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0002}\0" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 9 - TIME: 117.0832863 s

method {:test} Test9() {
var seqstring0 : seq<string> := ["", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\0aa");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\0aa" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 10 - TIME: 134.2573826 s
