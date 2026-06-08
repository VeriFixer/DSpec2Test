
method {:test} Test10() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 6048.0, 5968.0, 7523.0, 5045.0, 17790561.0 / 1250.0, 5189.0, 8746.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 9619.0, 6333.0, 0.0, 0.0, 119.0, 3577.0];
var r0 := has_close_elements(seqreal0, 11024.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 11024.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test11() {
var seqreal0 : seq<real> := [24065.0 / 2.0, 24384.0, 12301.0, 9402.0, 21171.0, 4718.0, -1224.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, -1.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < -1.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 6 - TIME: 11.3452608 s