predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}


method {:testEntry} CountDigits(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
    var digits := set i: int | 0 <= i < |s| && IsDigit(s[i]);
    count := |digits|;
}

method {:test} Test0() {
var r0 := CountDigits("1");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 2.6501357 s

method {:test} Test1() {
var r0 := CountDigits("aaaaaaaaaaaaa2aaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 3.5123461 s

method {:test} Test2() {
var r0 := CountDigits("a\0aaa1aaaaaaaaaaaaaaaaaaa\U{0001}aaa");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 4.4170062 s

method {:test} Test3() {
var r0 := CountDigits("\U{0002}aaaaaaaaaaa\0aaaaaaaaaaaa\U{0001}");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 5.2662082 s

method {:test} Test4() {
var r0 := CountDigits("aaaaaaaa0aaaaaaaaaaaaaaaa\0aaa\U{0001}");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 6.2982541 s

method {:test} Test5() {
var r0 := CountDigits("\U{0004}aaaaaaaaaaaaaaaaaaa\0aaaa\U{0001}\U{0002}aa\U{0003}");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 7.1096607 s

method {:test} Test6() {
var r0 := CountDigits("a1aaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 8.1191365 s

method {:test} Test7() {
var r0 := CountDigits("\0aaaaaa");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 8.9675372 s

method {:test} Test8() {
var r0 := CountDigits("\0aaaaaa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 9.8537217 s

method {:test} Test9() {
var r0 := CountDigits("\U{0001}\0");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 10.797014 s
