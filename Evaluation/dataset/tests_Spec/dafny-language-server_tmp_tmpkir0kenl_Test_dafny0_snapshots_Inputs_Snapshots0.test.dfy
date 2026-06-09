method {:testEntry} foo()
{
  bar();
  assert false;
}

method {:testEntry} bar()
  ensures false;

method {:test} Test0() {
foo();
}

// REPEAT 1 - TIME: 2.3757606 s

method {:test} Test1() {
foo();
}

// REPEAT 2 - TIME: 3.3059467 s

method {:test} Test2() {
foo();
}

// REPEAT 3 - TIME: 4.2971199 s

method {:test} Test3() {
foo();
}

// REPEAT 4 - TIME: 5.0707977 s

method {:test} Test4() {
foo();
}

// REPEAT 5 - TIME: 5.9454973 s

method {:test} Test5() {
foo();
}

// REPEAT 6 - TIME: 6.6353438 s

method {:test} Test6() {
foo();
}

// REPEAT 7 - TIME: 7.2737852 s

method {:test} Test7() {
foo();
}

// REPEAT 8 - TIME: 7.8490627 s

method {:test} Test8() {
foo();
}

// REPEAT 9 - TIME: 8.4488498 s

method {:test} Test9() {
foo();
}

// REPEAT 10 - TIME: 9.0288506 s
