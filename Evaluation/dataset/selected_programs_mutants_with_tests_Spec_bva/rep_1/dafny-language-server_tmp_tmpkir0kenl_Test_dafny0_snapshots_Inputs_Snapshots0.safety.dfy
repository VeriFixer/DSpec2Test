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
