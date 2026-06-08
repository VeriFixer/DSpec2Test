
method {:test} Test21() {
var seqreal0 : seq<real> := [23338.0, 0.0, 0.0, 5920.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect 17418.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := has_close_elements(seqreal0, 17418.0);
expect r0 ==> exists i: int, j: int :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && (if seqreal0[i] - seqreal0[j] < 0.0 then seqreal0[j] - seqreal0[i] else seqreal0[i] - seqreal0[j]) < 17418.0;
expect !r0 ==> forall i: int, j: int :: 1 <= i < |seqreal0| && 0 <= j < i ==> (if seqreal0[i] - seqreal0[j] < 0.0 then seqreal0[j] - seqreal0[i] else seqreal0[i] - seqreal0[j]) >= 17418.0;
}
method {:test} Test22() {
var seqreal0 : seq<real> := [7719.0, 15439.0 / 2.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 5.0, 13.0, 0.0, 0.0, 0.0, 0.0, 15.0, 0.0, 0.0, 0.0, 0.0, 0.0, 17.0, 0.0, 0.0, 0.0, 19.0, 21.0, 9.0, 0.0, 0.0, 0.0, 23.0];
expect 22269.0/2.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := has_close_elements(seqreal0, 22269.0/2.0);
expect r0 ==> exists i: int, j: int :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && (if seqreal0[i] - seqreal0[j] < 0.0 then seqreal0[j] - seqreal0[i] else seqreal0[i] - seqreal0[j]) < 22269.0/2.0;
expect !r0 ==> forall i: int, j: int :: 1 <= i < |seqreal0| && 0 <= j < i ==> (if seqreal0[i] - seqreal0[j] < 0.0 then seqreal0[j] - seqreal0[i] else seqreal0[i] - seqreal0[j]) >= 22269.0/2.0;
}

// REPEAT 4 - TIME: 15.083775 s