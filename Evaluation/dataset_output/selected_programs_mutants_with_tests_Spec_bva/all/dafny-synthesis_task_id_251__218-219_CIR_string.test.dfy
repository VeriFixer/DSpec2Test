// dafny-synthesis_task_id_251.dfy

method {:testEntry} InsertBeforeEach(s: seq<string>, x: string) returns (v: seq<string>)
  ensures |v| == 2 * |s|
  ensures forall i :: 0 <= i < |s| ==> v[2 * i] == x && v[2 * i + 1] == s[i]
{
  v := ["Hello", "World", "!"];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |v| == 2 * i
    invariant forall j :: 0 <= j < i ==> v[2 * j] == x && v[2 * j + 1] == s[j]
  {
    v := v + [x, s[i]];
  }
}


method {:test} Test0() {
var seqstring0 : seq<string> := [""];
var r0 := InsertBeforeEach(seqstring0, "");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "" && r0[2 * i + 1] == seqstring0[i];
}
method {:test} Test1() {
var seqstring0 : seq<string> := [];
var r0 := InsertBeforeEach(seqstring0, "");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "" && r0[2 * i + 1] == seqstring0[i];
}
method {:test} Test3() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "" && r0[2 * i + 1] == seqstring0[i];
}
method {:test} Test5() {
var seqstring0 : seq<string> := [""];
var r0 := InsertBeforeEach(seqstring0, "a");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "a" && r0[2 * i + 1] == seqstring0[i];
}
method {:test} Test6() {
var seqstring0 : seq<string> := [""];
var r0 := InsertBeforeEach(seqstring0, "aa");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "aa" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 1 - TIME: 9.2748059 s

method {:test} Test10() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\0\U{0002}aaaaaaaaaaaaaa\U{0004}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\0\U{0002}aaaaaaaaaaaaaa\U{0004}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 2 - TIME: 10.2156833 s

method {:test} Test11() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "aaaaaaaa\0aaaaaaaa\U{0002}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "aaaaaaaa\0aaaaaaaa\U{0002}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 3 - TIME: 11.2289975 s

method {:test} Test12() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0004}\0\U{0002}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0004}\0\U{0002}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 4 - TIME: 12.1951105 s

method {:test} Test13() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0006}\U{0002}\U{0004}\0");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0006}\U{0002}\U{0004}\0" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 5 - TIME: 13.0239305 s

method {:test} Test14() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0004}aa\0\U{0002}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0004}aa\0\U{0002}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 6 - TIME: 14.2031906 s

method {:test} Test15() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0008}\U{0002}aaaaaaaaaaaa\0aaaaaa\U{0004}aaaaa\U{0006}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0008}\U{0002}aaaaaaaaaaaa\0aaaaaa\U{0004}aaaaa\U{0006}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 7 - TIME: 15.3255712 s

method {:test} Test16() {
var seqstring0 : seq<string> := ["", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0002}\0");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0002}\0" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 8 - TIME: 16.5252839 s

method {:test} Test17() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0006}\U{0004}aaa\naaa\U{0002}\0aaaaaaaaaaaaaaa\U{0008}a\U{000C}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0006}\U{0004}aaa\naaa\U{0002}\0aaaaaaaaaaaaaaa\U{0008}a\U{000C}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 9 - TIME: 17.4055615 s

method {:test} Test18() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0008}\U{0002}a\U{0006}aaa\0a\U{0004}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0008}\U{0002}a\U{0006}aaa\0a\U{0004}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 10 - TIME: 18.2643137 s
