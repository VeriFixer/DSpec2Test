
method {:test} Test25() {
var seqreal0 : seq<real> := [39276113.0 / 1000.0, 8586.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1235.0, 0.0, 0.0, 0.0, 0.0, 0.0, 6906.0, 3609.0, 2616.0];
var r0 := has_close_elements(seqreal0, 74819.0/2.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 74819.0/2.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test26() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 107967.0 / 2.0, 0.0, 0.0, 0.0, 7719.0];
var r0 := has_close_elements(seqreal0, 92529.0/2.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 92529.0/2.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 6 - TIME: 16.3279932 s