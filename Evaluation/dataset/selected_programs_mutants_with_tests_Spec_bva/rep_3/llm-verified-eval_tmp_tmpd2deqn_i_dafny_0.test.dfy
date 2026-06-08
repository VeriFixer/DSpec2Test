
method {:test} Test19() {
var seqreal0 : seq<real> := [2211.0, 1594.0, 8221.0, -(29854133.0 / 4000.0), 582.0, 1108.0];
var r0 := has_close_elements(seqreal0, 35427.0/2.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 35427.0/2.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test20() {
var seqreal0 : seq<real> := [68575.0 / 2.0, 7719.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 53137.0/2.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 53137.0/2.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 3 - TIME: 12.5075477 s