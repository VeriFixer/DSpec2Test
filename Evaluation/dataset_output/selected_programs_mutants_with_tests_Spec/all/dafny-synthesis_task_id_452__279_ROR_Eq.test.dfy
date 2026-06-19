// dafny-synthesis_task_id_452.dfy

method {:testEntry} CalculateLoss(costPrice: int, sellingPrice: int) returns (loss: int)
  requires costPrice >= 0 && sellingPrice >= 0
  ensures (costPrice > sellingPrice ==> loss == costPrice - sellingPrice) && (costPrice <= sellingPrice ==> loss == 0)
{
  if costPrice == sellingPrice {
    loss := costPrice - sellingPrice;
  } else {
    loss := 0;
  }
}


method {:test} Test0() {
expect 0 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(0, 0);
expect (0 > 0 ==> r0 == 0 - 0) && (0 <= 0 ==> r0 == 0);
}
method {:test} Test1() {
expect 1 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(1, 0);
expect (1 > 0 ==> r0 == 1 - 0) && (1 <= 0 ==> r0 == 0);
}

// REPEAT 1 - TIME: 3.4770816 s

method {:test} Test2() {
expect 2 >= 0 && 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(2, 2);
expect (2 > 2 ==> r0 == 2 - 2) && (2 <= 2 ==> r0 == 0);
}
method {:test} Test3() {
expect 2 >= 0 && 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(2, 1);
expect (2 > 1 ==> r0 == 2 - 1) && (2 <= 1 ==> r0 == 0);
}

// REPEAT 2 - TIME: 5.174095 s

method {:test} Test4() {
expect 3 >= 0 && 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(3, 3);
expect (3 > 3 ==> r0 == 3 - 3) && (3 <= 3 ==> r0 == 0);
}
method {:test} Test5() {
expect 4 >= 0 && 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(4, 3);
expect (4 > 3 ==> r0 == 4 - 3) && (4 <= 3 ==> r0 == 0);
}

// REPEAT 3 - TIME: 6.6047002 s

method {:test} Test6() {
expect 5 >= 0 && 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(5, 5);
expect (5 > 5 ==> r0 == 5 - 5) && (5 <= 5 ==> r0 == 0);
}
method {:test} Test7() {
expect 5 >= 0 && 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(5, 4);
expect (5 > 4 ==> r0 == 5 - 4) && (5 <= 4 ==> r0 == 0);
}

// REPEAT 4 - TIME: 7.9436906 s

method {:test} Test8() {
expect 6 >= 0 && 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(6, 6);
expect (6 > 6 ==> r0 == 6 - 6) && (6 <= 6 ==> r0 == 0);
}
method {:test} Test9() {
expect 7 >= 0 && 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(7, 6);
expect (7 > 6 ==> r0 == 7 - 6) && (7 <= 6 ==> r0 == 0);
}

// REPEAT 5 - TIME: 9.5693358 s

method {:test} Test10() {
expect 8 >= 0 && 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(8, 8);
expect (8 > 8 ==> r0 == 8 - 8) && (8 <= 8 ==> r0 == 0);
}
method {:test} Test11() {
expect 8 >= 0 && 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(8, 7);
expect (8 > 7 ==> r0 == 8 - 7) && (8 <= 7 ==> r0 == 0);
}

// REPEAT 6 - TIME: 10.965889 s

method {:test} Test12() {
expect 9 >= 0 && 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(9, 9);
expect (9 > 9 ==> r0 == 9 - 9) && (9 <= 9 ==> r0 == 0);
}
method {:test} Test13() {
expect 10 >= 0 && 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(10, 9);
expect (10 > 9 ==> r0 == 10 - 9) && (10 <= 9 ==> r0 == 0);
}

// REPEAT 7 - TIME: 12.4401142 s

method {:test} Test14() {
expect 11 >= 0 && 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(11, 11);
expect (11 > 11 ==> r0 == 11 - 11) && (11 <= 11 ==> r0 == 0);
}
method {:test} Test15() {
expect 11 >= 0 && 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(11, 10);
expect (11 > 10 ==> r0 == 11 - 10) && (11 <= 10 ==> r0 == 0);
}

// REPEAT 8 - TIME: 13.7604487 s

method {:test} Test16() {
expect 12 >= 0 && 12 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(12, 12);
expect (12 > 12 ==> r0 == 12 - 12) && (12 <= 12 ==> r0 == 0);
}
method {:test} Test17() {
expect 13 >= 0 && 12 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(13, 12);
expect (13 > 12 ==> r0 == 13 - 12) && (13 <= 12 ==> r0 == 0);
}

// REPEAT 9 - TIME: 15.0970068 s

method {:test} Test18() {
expect 14 >= 0 && 14 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(14, 14);
expect (14 > 14 ==> r0 == 14 - 14) && (14 <= 14 ==> r0 == 0);
}
method {:test} Test19() {
expect 14 >= 0 && 13 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(14, 13);
expect (14 > 13 ==> r0 == 14 - 13) && (14 <= 13 ==> r0 == 0);
}

// REPEAT 10 - TIME: 16.4275318 s
