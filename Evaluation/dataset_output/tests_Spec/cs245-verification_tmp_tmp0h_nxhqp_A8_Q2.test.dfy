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

// REPEAT 1 - TIME: 2.8550715 s

method {:test} Test1() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(1, 1, 1);
expect r0 <= 1 && r0 <= 1 && r0 <= 1;
}

// REPEAT 2 - TIME: 3.8152168 s

method {:test} Test2() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(2, 2, 2);
expect r0 <= 2 && r0 <= 2 && r0 <= 2;
}

// REPEAT 3 - TIME: 4.7000913 s

method {:test} Test3() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(3, 3, 3);
expect r0 <= 3 && r0 <= 3 && r0 <= 3;
}

// REPEAT 4 - TIME: 5.5655429 s

method {:test} Test4() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(4, 4, 4);
expect r0 <= 4 && r0 <= 4 && r0 <= 4;
}

// REPEAT 5 - TIME: 6.3771759 s

method {:test} Test5() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(5, 5, 5);
expect r0 <= 5 && r0 <= 5 && r0 <= 5;
}

// REPEAT 6 - TIME: 7.2241354 s

method {:test} Test6() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(6, 6, 6);
expect r0 <= 6 && r0 <= 6 && r0 <= 6;
}

// REPEAT 7 - TIME: 8.1198106 s

method {:test} Test7() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(7, 7, 7);
expect r0 <= 7 && r0 <= 7 && r0 <= 7;
}

// REPEAT 8 - TIME: 9.0350565 s

method {:test} Test8() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(8, 8, 8);
expect r0 <= 8 && r0 <= 8 && r0 <= 8;
}

// REPEAT 9 - TIME: 9.8748503 s

method {:test} Test9() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(9, 9, 9);
expect r0 <= 9 && r0 <= 9 && r0 <= 9;
}

// REPEAT 10 - TIME: 10.6456712 s
