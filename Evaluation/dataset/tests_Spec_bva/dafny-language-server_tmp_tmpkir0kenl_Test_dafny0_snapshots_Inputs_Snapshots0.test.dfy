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

// REPEAT 1 - TIME: 3.4013022 s

method {:test} Test3() {
foo();
}

// REPEAT 2 - TIME: 4.2792306 s

method {:test} Test4() {
foo();
}

// REPEAT 3 - TIME: 5.4199235 s

method {:test} Test5() {
foo();
}

// REPEAT 4 - TIME: 6.3817627 s

method {:test} Test6() {
foo();
}

// REPEAT 5 - TIME: 7.4673132 s

method {:test} Test7() {
foo();
}

// REPEAT 6 - TIME: 8.4519258 s

method {:test} Test8() {
foo();
}

// REPEAT 7 - TIME: 9.3276117 s

method {:test} Test9() {
foo();
}

// REPEAT 8 - TIME: 10.2417313 s

method {:test} Test10() {
foo();
}

// REPEAT 9 - TIME: 10.9290556 s

method {:test} Test11() {
foo();
}

// REPEAT 10 - TIME: 11.5844784 s
