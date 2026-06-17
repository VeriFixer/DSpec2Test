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
method {:test} Test1() {
var seqstring0 : seq<string> := [];
var r0 := InsertBeforeEach(seqstring0, "");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "" && r0[2 * i + 1] == seqstring0[i];
}
method {:test} Test3() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
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

// REPEAT 1 - TIME: 7.3697434 s

method {:test} Test10() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\0\U{0002}a");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\0\U{0002}a" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 2 - TIME: 8.1671479 s

method {:test} Test11() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 3 - TIME: 8.9471763 s

method {:test} Test12() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 4 - TIME: 9.609928 s

method {:test} Test13() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 5 - TIME: 10.3432703 s

method {:test} Test14() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "a\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaa\U{0006}\U{0008}\n");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "a\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaa\U{0006}\U{0008}\n" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 6 - TIME: 11.2236035 s

method {:test} Test15() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0004}\U{0002}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaa\0aaaaaaaaaa\U{0008}\n\U{000C}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0004}\U{0002}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaa\0aaaaaaaaaa\U{0008}\n\U{000C}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 7 - TIME: 12.0381185 s

method {:test} Test16() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}aaaa\U{0008}a\0\n");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}aaaa\U{0008}a\0\n" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 8 - TIME: 12.845601 s

method {:test} Test17() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "a\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0006}aaaaaa\0aaaaaaaa\U{0008}\naa\U{000C}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "a\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0006}aaaaaa\0aaaaaaaa\U{0008}\naa\U{000C}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 9 - TIME: 13.5387697 s

method {:test} Test18() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0008}\n\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaa\U{0004}\U{0006}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0008}\n\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaa\U{0004}\U{0006}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 10 - TIME: 14.5729506 s
