
method {:test} Test2() {
var seqreal0 : seq<real> := [8098.0, 1796.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2195613.0 / 1000.0];
var r0 := has_close_elements(seqreal0, 2440.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 2440.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test3() {
var seqreal0 : seq<real> := [0.0];
var r0 := has_close_elements(seqreal0, 1.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 1.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 2 - TIME: 4.2225435 s