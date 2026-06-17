// dafny-synthesis_task_id_251.dfy

method {:testEntry} InsertBeforeEach(s: seq<string>, x: string) returns (v: seq<string>)
  ensures |v| == 2 * |s|
  ensures forall i :: 0 <= i < |s| ==> v[2 * i] == x && v[2 * i + 1] == s[i]
{
  v := [];
  for i := -1 to |s|
    invariant 0 <= i <= |s|
    invariant |v| == 2 * i
    invariant forall j :: 0 <= j < i ==> v[2 * j] == x && v[2 * j + 1] == s[j]
  {
    v := v + [x, s[i]];
  }
}


method {:testEntry} InsertBeforeEach(s: seq<string>, x: string) returns (v: seq<string>)
        ensures |v| == 2 * |s|
        ensures forall i :: 0 <= i < |s| ==> v[2*i] == x && v[2*i + 1] == s[i]
    {
        v := [];
        for i := 0 to |s|
            invariant 0 <= i <= |s|
            invariant |v| == 2 * i
            invariant forall j :: 0 <= j < i ==> v[2*j] == x && v[2*j + 1] == s[j]
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

// REPEAT 1 - TIME: 2.2374922 s

method {:test} Test1() {
var seqstring0 : seq<string> := ["", ""];
var r0 := InsertBeforeEach(seqstring0, "aaaaaaaaaaaaaaaaaaa\0");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "aaaaaaaaaaaaaaaaaaa\0" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 2 - TIME: 3.1010844 s

method {:test} Test2() {
var seqstring0 : seq<string> := ["", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0002}aaaaaaaaaaaaaaaaaa\0");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0002}aaaaaaaaaaaaaaaaaa\0" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 3 - TIME: 4.0170502 s

method {:test} Test3() {
var seqstring0 : seq<string> := ["", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0004}aaaaaaaaaaa\0aaaaaaa\U{0002}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0004}aaaaaaaaaaa\0aaaaaaa\U{0002}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 4 - TIME: 4.781647 s

method {:test} Test4() {
var seqstring0 : seq<string> := ["", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "aaaaaaaa\0aaaaaaaaaaa\U{0002}\U{0004}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "aaaaaaaa\0aaaaaaaaaaa\U{0002}\U{0004}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 5 - TIME: 5.6957286 s

method {:test} Test5() {
var seqstring0 : seq<string> := ["", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "aaaaaaaaa\0aaaaaaaaaa\U{0002}a\U{0004}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "aaaaaaaaa\0aaaaaaaaaa\U{0002}a\U{0004}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 6 - TIME: 6.4839727 s

method {:test} Test6() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "a");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "a" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 7 - TIME: 7.2871331 s

method {:test} Test7() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0002}\0");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0002}\0" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 8 - TIME: 8.0847495 s

method {:test} Test8() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0002}aaaaaaaaaaaaaaa\0aaaa\U{0004}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0002}aaaaaaaaaaaaaaa\0aaaa\U{0004}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 9 - TIME: 8.8691067 s

method {:test} Test9() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\0");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\0" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 10 - TIME: 9.6058937 s
