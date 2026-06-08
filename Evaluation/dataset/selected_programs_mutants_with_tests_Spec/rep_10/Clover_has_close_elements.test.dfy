
method {:test} Test18() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 5853.0, 0.0];
expect 29463.0/2.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := has_close_elements(seqreal0, 29463.0/2.0);
expect r0 ==> exists i: int, j: int :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && (if seqreal0[i] - seqreal0[j] < 0.0 then seqreal0[j] - seqreal0[i] else seqreal0[i] - seqreal0[j]) < 29463.0/2.0;
expect !r0 ==> forall i: int, j: int :: 1 <= i < |seqreal0| && 0 <= j < i ==> (if seqreal0[i] - seqreal0[j] < 0.0 then seqreal0[j] - seqreal0[i] else seqreal0[i] - seqreal0[j]) >= 29463.0/2.0;
}
method {:test} Test19() {
var seqreal0 : seq<real> := [7719.0, 20313.0 / 2.0, 0.0, 0.0, 21.0, 19.0, 0.0, 11.0, 23.0, 15.0, 0.0, 0.0];
expect 17168.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := has_close_elements(seqreal0, 17168.0);
expect r0 ==> exists i: int, j: int :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && (if seqreal0[i] - seqreal0[j] < 0.0 then seqreal0[j] - seqreal0[i] else seqreal0[i] - seqreal0[j]) < 17168.0;
expect !r0 ==> forall i: int, j: int :: 1 <= i < |seqreal0| && 0 <= j < i ==> (if seqreal0[i] - seqreal0[j] < 0.0 then seqreal0[j] - seqreal0[i] else seqreal0[i] - seqreal0[j]) >= 17168.0;
}

// REPEAT 10 - TIME: 14.219405 s