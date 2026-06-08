
method {:test} Test19() {
var seqreal0 : seq<real> := [449.0];
expect 7.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := has_close_elements(seqreal0, 7.0);
expect r0 ==> exists i: int, j: int :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && (if seqreal0[i] - seqreal0[j] < 0.0 then seqreal0[j] - seqreal0[i] else seqreal0[i] - seqreal0[j]) < 7.0;
expect !r0 ==> forall i: int, j: int :: 1 <= i < |seqreal0| && 0 <= j < i ==> (if seqreal0[i] - seqreal0[j] < 0.0 then seqreal0[j] - seqreal0[i] else seqreal0[i] - seqreal0[j]) >= 7.0;
}

// REPEAT 8 - TIME: 18.6844133 s