
method {:test} Test10() {
var seqreal0 : seq<real> := [210657374081.0 / 7500000.0, 273394874081.0 / 15000000.0, 8365.0, -(22444874081.0 / 15000000.0), -(176042295919.0 / 15000000.0)];
expect 147919874081.0/15000000.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := has_close_elements(seqreal0, 147919874081.0/15000000.0);
expect r0 ==> exists i: int, j: int :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && (if seqreal0[i] - seqreal0[j] < 0.0 then seqreal0[j] - seqreal0[i] else seqreal0[i] - seqreal0[j]) < 147919874081.0/15000000.0;
expect !r0 ==> forall i: int, j: int :: 1 <= i < |seqreal0| && 0 <= j < i ==> (if seqreal0[i] - seqreal0[j] < 0.0 then seqreal0[j] - seqreal0[i] else seqreal0[i] - seqreal0[j]) >= 147919874081.0/15000000.0;
}
method {:test} Test11() {
var seqreal0 : seq<real> := [15437.0 / 2.0, 10156.0];
expect 22597.0/2.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := has_close_elements(seqreal0, 22597.0/2.0);
expect r0 ==> exists i: int, j: int :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && (if seqreal0[i] - seqreal0[j] < 0.0 then seqreal0[j] - seqreal0[i] else seqreal0[i] - seqreal0[j]) < 22597.0/2.0;
expect !r0 ==> forall i: int, j: int :: 1 <= i < |seqreal0| && 0 <= j < i ==> (if seqreal0[i] - seqreal0[j] < 0.0 then seqreal0[j] - seqreal0[i] else seqreal0[i] - seqreal0[j]) >= 22597.0/2.0;
}

// REPEAT 6 - TIME: 10.0366992 s