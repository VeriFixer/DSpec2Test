// dafny-synthesis_task_id_452.dfy

method {:testEntry} CalculateLoss(costPrice: int, sellingPrice: int) returns (loss: int)
  requires costPrice >= 0 && sellingPrice >= 0
  ensures (costPrice > sellingPrice ==> loss == costPrice - sellingPrice) && (costPrice <= sellingPrice ==> loss == 0)
{
  if false {
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
method {:test} Test2() {
expect 100 >= 0 && 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(100, 100);
expect (100 > 100 ==> r0 == 100 - 100) && (100 <= 100 ==> r0 == 0);
}
method {:test} Test4() {
expect 0 >= 0 && 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(0, 100);
expect (0 > 100 ==> r0 == 0 - 100) && (0 <= 100 ==> r0 == 0);
}
method {:test} Test8() {
expect 1 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(1, 0);
expect (1 > 0 ==> r0 == 1 - 0) && (1 <= 0 ==> r0 == 0);
}
method {:test} Test9() {
expect 100 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(100, 0);
expect (100 > 0 ==> r0 == 100 - 0) && (100 <= 0 ==> r0 == 0);
}
method {:test} Test11() {
expect 101 >= 0 && 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(101, 100);
expect (101 > 100 ==> r0 == 101 - 100) && (101 <= 100 ==> r0 == 0);
}

// REPEAT 1 - TIME: 14.2357456 s

method {:test} Test16() {
expect 102 >= 0 && 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(102, 102);
expect (102 > 102 ==> r0 == 102 - 102) && (102 <= 102 ==> r0 == 0);
}
method {:test} Test17() {
expect 102 >= 0 && 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(102, 101);
expect (102 > 101 ==> r0 == 102 - 101) && (102 <= 101 ==> r0 == 0);
}

// REPEAT 2 - TIME: 15.9081153 s

method {:test} Test18() {
expect 103 >= 0 && 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(103, 103);
expect (103 > 103 ==> r0 == 103 - 103) && (103 <= 103 ==> r0 == 0);
}
method {:test} Test19() {
expect 104 >= 0 && 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(104, 103);
expect (104 > 103 ==> r0 == 104 - 103) && (104 <= 103 ==> r0 == 0);
}

// REPEAT 3 - TIME: 17.5366562 s

method {:test} Test20() {
expect 105 >= 0 && 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(105, 105);
expect (105 > 105 ==> r0 == 105 - 105) && (105 <= 105 ==> r0 == 0);
}
method {:test} Test21() {
expect 105 >= 0 && 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(105, 104);
expect (105 > 104 ==> r0 == 105 - 104) && (105 <= 104 ==> r0 == 0);
}

// REPEAT 4 - TIME: 18.8585245 s

method {:test} Test22() {
expect 106 >= 0 && 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(106, 106);
expect (106 > 106 ==> r0 == 106 - 106) && (106 <= 106 ==> r0 == 0);
}
method {:test} Test23() {
expect 107 >= 0 && 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(107, 106);
expect (107 > 106 ==> r0 == 107 - 106) && (107 <= 106 ==> r0 == 0);
}

// REPEAT 5 - TIME: 20.1092313 s

method {:test} Test24() {
expect 108 >= 0 && 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(108, 108);
expect (108 > 108 ==> r0 == 108 - 108) && (108 <= 108 ==> r0 == 0);
}
method {:test} Test25() {
expect 108 >= 0 && 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(108, 107);
expect (108 > 107 ==> r0 == 108 - 107) && (108 <= 107 ==> r0 == 0);
}

// REPEAT 6 - TIME: 21.3507241 s

method {:test} Test26() {
expect 109 >= 0 && 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(109, 109);
expect (109 > 109 ==> r0 == 109 - 109) && (109 <= 109 ==> r0 == 0);
}
method {:test} Test27() {
expect 110 >= 0 && 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(110, 109);
expect (110 > 109 ==> r0 == 110 - 109) && (110 <= 109 ==> r0 == 0);
}

// REPEAT 7 - TIME: 22.6320975 s

method {:test} Test28() {
expect 111 >= 0 && 111 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(111, 111);
expect (111 > 111 ==> r0 == 111 - 111) && (111 <= 111 ==> r0 == 0);
}
method {:test} Test29() {
expect 111 >= 0 && 110 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(111, 110);
expect (111 > 110 ==> r0 == 111 - 110) && (111 <= 110 ==> r0 == 0);
}

// REPEAT 8 - TIME: 23.6856845 s

method {:test} Test30() {
expect 112 >= 0 && 112 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(112, 112);
expect (112 > 112 ==> r0 == 112 - 112) && (112 <= 112 ==> r0 == 0);
}
method {:test} Test31() {
expect 113 >= 0 && 112 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(113, 112);
expect (113 > 112 ==> r0 == 113 - 112) && (113 <= 112 ==> r0 == 0);
}

// REPEAT 9 - TIME: 25.167881 s

method {:test} Test32() {
expect 114 >= 0 && 114 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(114, 114);
expect (114 > 114 ==> r0 == 114 - 114) && (114 <= 114 ==> r0 == 0);
}
method {:test} Test33() {
expect 114 >= 0 && 113 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(114, 113);
expect (114 > 113 ==> r0 == 114 - 113) && (114 <= 113 ==> r0 == 0);
}

// REPEAT 10 - TIME: 26.3948457 s
