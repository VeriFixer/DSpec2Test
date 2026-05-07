include "/home/ricostynha/Desktop/SpecTestGenerator/Evaluation/dataset/selected_programs/Correctness_tmp_tmpwqvg5q_4_HoareLogic_exam.dfy"
method {:test} Test0() {
expect 1 > 0 && 39 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GCD1(1, 39);
expect gcd(1, 39) == r0;
}
method {:test} Test1() {
expect 1 > 0 && 38 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GCD2(1, 38);
expect gcd(1, 38) == r0;
}


