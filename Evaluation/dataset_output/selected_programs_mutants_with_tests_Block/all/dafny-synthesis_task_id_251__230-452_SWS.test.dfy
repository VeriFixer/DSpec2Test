// dafny-synthesis_task_id_251.dfy

method {:testEntry} InsertBeforeEach(s: seq<string>, x: string) returns (v: seq<string>)
  ensures |v| == 2 * |s|
  ensures forall i :: 0 <= i < |s| ==> v[2 * i] == x && v[2 * i + 1] == s[i]
{
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |v| == 2 * i
    invariant forall j :: 0 <= j < i ==> v[2 * j] == x && v[2 * j + 1] == s[j]
  {
    v := v + [x, s[i]];
  }
  v := [];
}


method {:test} Test0() {
var seqstring0 : seq<string> := [""];
var r0 := InsertBeforeEach(seqstring0, "");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 1 - TIME: 2.5478741 s

method {:test} Test1() {
var seqstring0 : seq<string> := ["", ""];
var r0 := InsertBeforeEach(seqstring0, "aaaaaaaaa\0");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "aaaaaaaaa\0" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 2 - TIME: 3.3400835 s

method {:test} Test2() {
var seqstring0 : seq<string> := ["", "", ""];
var r0 := InsertBeforeEach(seqstring0, "aaaaaaaa\0a\U{0002}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "aaaaaaaa\0a\U{0002}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 3 - TIME: 4.176055 s

method {:test} Test3() {
var seqstring0 : seq<string> := ["", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "aaa\0aaaaaa\U{0002}\U{0004}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "aaa\0aaaaaa\U{0002}\U{0004}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 4 - TIME: 5.1304005 s

method {:test} Test4() {
var seqstring0 : seq<string> := ["", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\0aaaaaaaaaaa\U{0002}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\0aaaaaaaaaaa\U{0002}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 5 - TIME: 6.1431249 s

method {:test} Test5() {
var seqstring0 : seq<string> := ["", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0002}aaaaa\0");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0002}aaaaa\0" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 6 - TIME: 7.0528948 s

method {:test} Test6() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0008}aaaaaaa\U{0002}\0\U{0004}\U{0006}a");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0008}aaaaaaa\U{0002}\0\U{0004}\U{0006}a" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 7 - TIME: 7.8610588 s

method {:test} Test7() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "aaaaaaaaaaaaaa");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "aaaaaaaaaaaaaa" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 8 - TIME: 8.5995776 s

method {:test} Test8() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0002}aaaaaaaaaa\U{0004}a\0\U{0006}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0002}aaaaaaaaaa\U{0004}a\0\U{0006}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 9 - TIME: 9.3364919 s

method {:test} Test9() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0002}aaaaa\0aaa\U{0004}\U{0006}\U{0008}\U{000C}\n\U{000E}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0002}aaaaa\0aaa\U{0004}\U{0006}\U{0008}\U{000C}\n\U{000E}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 10 - TIME: 10.1825034 s
