
method {:test} Test8() {
var seqreal0 : seq<real> := [7629.0, 7578.0, 2379.0, 2211.0, 0.0, 0.0, 1108.0, 582.0, 0.0, 7065.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 10541.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 10541.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test9() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 55955.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 44932.0, 33909.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 22886.0, 11863.0, 840.0, 0.0];
var r0 := has_close_elements(seqreal0, 11023.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 11023.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 5 - TIME: 8.6663835 s