// A8Q2 — Steph Renee McIntyre
// Following the solutions from Carmen Bruni

method {:testEntry} A8Q1(x: int, y: int, z: int) returns (m: int)
/*Pre-Condition*/   requires true;
/*Post-Condition*/  ensures m<=x && m<=y && m<=z;
{ 
  /* (| true |)                               - Pre-Condition */
      if(z<y){
      /* (| z<y |)                            - if-then-else  */   
          if(z<x){
            /* (| z<y ^ z<=x |)               - if-then-else  */  
            /* (| z<=x ^ z<=y ^ z<=z |)       - implied (a)   */  
                m := z;
            /* (| m<=x ^ m<=y ^ m<=z |)       - assignment    */  
          }else{
            /* (| z<y ^ -(z<=x) |)            - if-then-else  */  
            /* (| x<=x ^ x<=y ^ x<=z |)       - implied (b)   */  
                m := x;
            /* (| m<=x ^ m<=y ^ m<=z |)       - assignment    */  
          }
      }else{
      /* (| -(z<y) |)                         - if-then-else  */  
      /* (| y<=y ^ y<=z |)                    - implied (c)   */  
          m := y;
      /* (| m<=y ^ y<=z |)                    - assignment    */  
          if (x<y){
            /* (| m<=y ^ y<=z ^ x<y |)        - if-then       */  
            /* (| x<=x ^ x<=y ^ x<=z |)       - implied (d)   */  
                m := x;
            /* (| m<=x ^ m<=y ^ m<=z |)       - assignment    */  
          }
      /* (| m<=x ^ m<=y ^ m<=z |)             - if-then: implied (e) */  
      }
  /* (| m<=x ^ m<=y ^ m<=z |)                 - if-then-else  */  
}

/* Proof of implieds can be seen on LEARN.
    Note: If you are unconvinced, putting asserts for each condition will demonstrate the correctness of the statements. 
*/

method {:test} Test0() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(0, 0, 0);
expect r0 <= 0 && r0 <= 0 && r0 <= 0;
}
method {:test} Test1() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(-100, 0, 0);
expect r0 <= -100 && r0 <= 0 && r0 <= 0;
}
method {:test} Test2() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(100, 0, 0);
expect r0 <= 100 && r0 <= 0 && r0 <= 0;
}
method {:test} Test3() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(0, -100, 0);
expect r0 <= 0 && r0 <= -100 && r0 <= 0;
}
method {:test} Test4() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(0, 100, 0);
expect r0 <= 0 && r0 <= 100 && r0 <= 0;
}
method {:test} Test5() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(0, 0, -100);
expect r0 <= 0 && r0 <= 0 && r0 <= -100;
}
method {:test} Test6() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(0, 0, 100);
expect r0 <= 0 && r0 <= 0 && r0 <= 100;
}
method {:test} Test9() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(100, 100, 100);
expect r0 <= 100 && r0 <= 100 && r0 <= 100;
}

// REPEAT 1 - TIME: 7.3885813 s

method {:test} Test12() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(101, 101, 101);
expect r0 <= 101 && r0 <= 101 && r0 <= 101;
}

// REPEAT 2 - TIME: 8.3419517 s

method {:test} Test13() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(102, 102, 102);
expect r0 <= 102 && r0 <= 102 && r0 <= 102;
}

// REPEAT 3 - TIME: 9.1842489 s

method {:test} Test14() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(103, 103, 103);
expect r0 <= 103 && r0 <= 103 && r0 <= 103;
}

// REPEAT 4 - TIME: 9.9227306 s

method {:test} Test15() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(104, 104, 104);
expect r0 <= 104 && r0 <= 104 && r0 <= 104;
}

// REPEAT 5 - TIME: 10.6977114 s

method {:test} Test16() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(105, 105, 105);
expect r0 <= 105 && r0 <= 105 && r0 <= 105;
}

// REPEAT 6 - TIME: 11.47418 s

method {:test} Test17() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(106, 106, 106);
expect r0 <= 106 && r0 <= 106 && r0 <= 106;
}

// REPEAT 7 - TIME: 12.1576943 s

method {:test} Test18() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(107, 107, 107);
expect r0 <= 107 && r0 <= 107 && r0 <= 107;
}

// REPEAT 8 - TIME: 12.9139748 s

method {:test} Test19() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(108, 108, 108);
expect r0 <= 108 && r0 <= 108 && r0 <= 108;
}

// REPEAT 9 - TIME: 13.7477611 s

method {:test} Test20() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(109, 109, 109);
expect r0 <= 109 && r0 <= 109 && r0 <= 109;
}

// REPEAT 10 - TIME: 14.3152762 s
