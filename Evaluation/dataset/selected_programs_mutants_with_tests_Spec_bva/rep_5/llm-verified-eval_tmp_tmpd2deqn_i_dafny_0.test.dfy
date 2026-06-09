
method {:test} Test23() {
var seqreal0 : seq<real> := [5981.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 334.0, 0.0, 3960.0, 238968963.0 / 10000.0, 6019.0, 1391.0, 624.0, 7065.0];
var r0 := has_close_elements(seqreal0, 61061.0/2.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 61061.0/2.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test24() {
var seqreal0 : seq<real> := [1323.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 77463.0 / 2.0, -(72171.0 / 2.0), -73494.0];
var r0 := has_close_elements(seqreal0, 74817.0/2.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 74817.0/2.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 5 - TIME: 13.4868728 s