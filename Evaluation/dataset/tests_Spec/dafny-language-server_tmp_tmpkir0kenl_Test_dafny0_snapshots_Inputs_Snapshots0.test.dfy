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

// REPEAT 1 - TIME: 2.8126355 s

method {:test} Test1() {
foo();
}

// REPEAT 2 - TIME: 3.67868 s

method {:test} Test2() {
foo();
}

// REPEAT 3 - TIME: 4.5667705 s

method {:test} Test3() {
foo();
}

// REPEAT 4 - TIME: 5.4301586 s

method {:test} Test4() {
foo();
}

// REPEAT 5 - TIME: 6.2395837 s

method {:test} Test5() {
foo();
}

// REPEAT 6 - TIME: 7.0794382 s

method {:test} Test6() {
foo();
}

// REPEAT 7 - TIME: 7.7186968 s

method {:test} Test7() {
foo();
}

// REPEAT 8 - TIME: 8.5235471 s

method {:test} Test8() {
foo();
}

// REPEAT 9 - TIME: 9.2417602 s

method {:test} Test9() {
foo();
}

// REPEAT 10 - TIME: 9.8727573 s
