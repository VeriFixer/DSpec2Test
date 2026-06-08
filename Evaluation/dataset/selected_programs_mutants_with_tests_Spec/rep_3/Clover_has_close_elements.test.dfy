
method {:test} Test4() {
var seqreal0 : seq<real> := [10095.0, 0.0, 1236.0];
expect 8859.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := has_close_elements(seqreal0, 8859.0);
expect r0 ==> exists i: int, j: int :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && (if seqreal0[i] - seqreal0[j] < 0.0 then seqreal0[j] - seqreal0[i] else seqreal0[i] - seqreal0[j]) < 8859.0;
expect !r0 ==> forall i: int, j: int :: 1 <= i < |seqreal0| && 0 <= j < i ==> (if seqreal0[i] - seqreal0[j] < 0.0 then seqreal0[j] - seqreal0[i] else seqreal0[i] - seqreal0[j]) >= 8859.0;
}
method {:test} Test5() {
var seqreal0 : seq<real> := [7719.0, 10157.0];
expect 2441.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := has_close_elements(seqreal0, 2441.0);
expect r0 ==> exists i: int, j: int :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && (if seqreal0[i] - seqreal0[j] < 0.0 then seqreal0[j] - seqreal0[i] else seqreal0[i] - seqreal0[j]) < 2441.0;
expect !r0 ==> forall i: int, j: int :: 1 <= i < |seqreal0| && 0 <= j < i ==> (if seqreal0[i] - seqreal0[j] < 0.0 then seqreal0[j] - seqreal0[i] else seqreal0[i] - seqreal0[j]) >= 2441.0;
}

// REPEAT 3 - TIME: 6.1068013 s