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

// REPEAT 1 - TIME: 2.9864428 s

method {:test} Test3() {
foo();
}

// REPEAT 2 - TIME: 3.6106232 s

method {:test} Test4() {
foo();
}

// REPEAT 3 - TIME: 4.2929846 s

method {:test} Test5() {
foo();
}

// REPEAT 4 - TIME: 5.0223319 s

method {:test} Test6() {
foo();
}

// REPEAT 5 - TIME: 5.7545477 s

method {:test} Test7() {
foo();
}

// REPEAT 6 - TIME: 6.718794 s

method {:test} Test8() {
foo();
}

// REPEAT 7 - TIME: 7.529658 s

method {:test} Test9() {
foo();
}

// REPEAT 8 - TIME: 8.1902458 s

method {:test} Test10() {
foo();
}

// REPEAT 9 - TIME: 8.7386532 s

method {:test} Test11() {
foo();
}

// REPEAT 10 - TIME: 9.2964399 s
