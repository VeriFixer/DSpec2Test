method {:testEntry} CountLists(lists: seq<seq<int>>) returns (count: int)
    ensures count >= 0
    ensures count == |lists|
{
    count := |lists|;
}

method {:test} Test0() {
var seqseqint0 : seq<seq<int>> := [];
var r0 := CountLists(seqseqint0);
expect r0 >= 0;
expect r0 == |seqseqint0|;
}

// REPEAT 1 - TIME: 2.2243264 s

method {:test} Test1() {
var seqint0 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0];
var r0 := CountLists(seqseqint0);
expect r0 >= 0;
expect r0 == |seqseqint0|;
}

// REPEAT 2 - TIME: 2.8867883 s

method {:test} Test2() {
var seqint0 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0];
var r0 := CountLists(seqseqint0);
expect r0 >= 0;
expect r0 == |seqseqint0|;
}

// REPEAT 3 - TIME: 3.6118892 s

method {:test} Test3() {
var seqint0 : seq<int> := [0, 0];
var seqint1 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
var r0 := CountLists(seqseqint0);
expect r0 >= 0;
expect r0 == |seqseqint0|;
}

// REPEAT 4 - TIME: 4.2864142 s

method {:test} Test4() {
var seqint0 : seq<int> := [0, 0, 0];
var seqint1 : seq<int> := [0, 0];
var seqint2 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2];
var r0 := CountLists(seqseqint0);
expect r0 >= 0;
expect r0 == |seqseqint0|;
}

// REPEAT 5 - TIME: 5.0298229 s

method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0];
var seqint2 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2];
var r0 := CountLists(seqseqint0);
expect r0 >= 0;
expect r0 == |seqseqint0|;
}

// REPEAT 6 - TIME: 5.782869 s

method {:test} Test6() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0];
var seqint2 : seq<int> := [0, 0];
var seqint3 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3];
var r0 := CountLists(seqseqint0);
expect r0 >= 0;
expect r0 == |seqseqint0|;
}

// REPEAT 7 - TIME: 6.599221 s

method {:test} Test7() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0];
var seqint2 : seq<int> := [0, 0, 0];
var seqint3 : seq<int> := [0];
var seqint4 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4];
var r0 := CountLists(seqseqint0);
expect r0 >= 0;
expect r0 == |seqseqint0|;
}

// REPEAT 8 - TIME: 7.32932 s

method {:test} Test8() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [0, 0, 0, 0];
var seqint3 : seq<int> := [0, 0];
var seqint4 : seq<int> := [0];
var seqint5 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5];
var r0 := CountLists(seqseqint0);
expect r0 >= 0;
expect r0 == |seqseqint0|;
}

// REPEAT 9 - TIME: 8.17037 s

method {:test} Test9() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [0, 0, 0, 0, 0];
var seqint3 : seq<int> := [0, 0, 0];
var seqint4 : seq<int> := [0, 0];
var seqint5 : seq<int> := [0];
var seqint6 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6];
var r0 := CountLists(seqseqint0);
expect r0 >= 0;
expect r0 == |seqseqint0|;
}

// REPEAT 10 - TIME: 8.889072 s
