// llm-verified-eval_tmp_tmpd2deqn_i_dafny_5.dfy

method {:testEntry} intersperse(numbers: seq<int>, delimiter: int) returns (interspersed: seq<int>)
  ensures |interspersed| == if |numbers| > 0 then 2 * |numbers| - 1 else 0
  ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 0 ==> interspersed[i] == numbers[i / 2]
  ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 1 ==> interspersed[i] == delimiter
{
  interspersed := [];
  for i := 0 to |numbers|
    invariant |interspersed| == if i > 0 then 2 * i - 1 else 0
    invariant forall i0 :: 0 <= i0 < |interspersed| ==> i0 % 2 == 0 ==> interspersed[i0] == numbers[i0 / 2]
    invariant forall i0 :: 0 <= i0 < |interspersed| ==> i0 % 2 == 1 ==> interspersed[i0] == delimiter
  {
    if i < 0 {
      interspersed := interspersed + [delimiter];
    }
    interspersed := interspersed + [numbers[i]];
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [0];
var r0 := intersperse(seqint0, 0);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 0;
}

// REPEAT 1 - TIME: 2.9318682 s

method {:test} Test2() {
var seqint0 : seq<int> := [1];
var r0 := intersperse(seqint0, 24);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 24;
}
method {:test} Test3() {
var seqint0 : seq<int> := [1, 0];
var r0 := intersperse(seqint0, 24);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 24;
}

// REPEAT 2 - TIME: 4.2838442 s

method {:test} Test4() {
var seqint0 : seq<int> := [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4];
var r0 := intersperse(seqint0, 25);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 25;
}
method {:test} Test5() {
var seqint0 : seq<int> := [2];
var r0 := intersperse(seqint0, 25);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 25;
}

// REPEAT 3 - TIME: 5.73888 s

method {:test} Test6() {
var seqint0 : seq<int> := [3];
var r0 := intersperse(seqint0, 27);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 27;
}
method {:test} Test7() {
var seqint0 : seq<int> := [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6];
var r0 := intersperse(seqint0, 26);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 26;
}

// REPEAT 4 - TIME: 7.2463593 s

method {:test} Test8() {
var seqint0 : seq<int> := [5, 0, 0, 0, 0, 0, 8, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 14];
var r0 := intersperse(seqint0, 28);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 28;
}
method {:test} Test9() {
var seqint0 : seq<int> := [5, 0, 0, 12, 0, 0, 8, 0, 0, 0, 0, 10, 0, 0, 14, 0, 0, 18, 16, 0, 0, 0, 20];
var r0 := intersperse(seqint0, 28);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 28;
}

// REPEAT 5 - TIME: 9.088373 s

method {:test} Test10() {
var seqint0 : seq<int> := [7, 0, 11];
var r0 := intersperse(seqint0, 29);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 29;
}
method {:test} Test11() {
var seqint0 : seq<int> := [7, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 15];
var r0 := intersperse(seqint0, 30);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 30;
}

// REPEAT 6 - TIME: 10.2885444 s

method {:test} Test12() {
var seqint0 : seq<int> := [9, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 21, 23];
var r0 := intersperse(seqint0, 31);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 31;
}
method {:test} Test13() {
var seqint0 : seq<int> := [9, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 25, 29, 23, 0, 27];
var r0 := intersperse(seqint0, 31);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 31;
}

// REPEAT 7 - TIME: 11.7692594 s

method {:test} Test14() {
var seqint0 : seq<int> := [13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 22, 26, 0, 0, 0, 0, 0, 32];
var r0 := intersperse(seqint0, 32);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 32;
}
method {:test} Test15() {
var seqint0 : seq<int> := [13, 0, 22, 26];
var r0 := intersperse(seqint0, 32);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 32;
}

// REPEAT 8 - TIME: 13.1761031 s

method {:test} Test16() {
var seqint0 : seq<int> := [19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := intersperse(seqint0, 33);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 33;
}

// REPEAT 9 - TIME: 14.5795776 s

method {:test} Test18() {
var seqint0 : seq<int> := [24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := intersperse(seqint0, 39);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 39;
}
method {:test} Test19() {
var seqint0 : seq<int> := [24, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 31, 0, 0, 0, 0, 0, 38];
var r0 := intersperse(seqint0, 34);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 34;
}

// REPEAT 10 - TIME: 16.11162 s
