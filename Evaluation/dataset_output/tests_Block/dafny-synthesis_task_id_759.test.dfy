method {:testEntry} IsDecimalWithTwoPrecision(s: string) returns (result: bool)
    ensures result ==> (exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
    ensures !result ==> !(exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
{
    result := false;
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant result <==> (exists k :: 0 <= k < i && s[k] == '.' && |s| - k - 1 == 2)
    {
        if s[i] == '.' && |s| - i - 1 == 2 {
            result := true;
            break;
        }
    }
}

method {:test} Test0() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
}
method {:test} Test1() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| - i - 1 == 2;
}

// REPEAT 1 - TIME: 3.0264807 s

method {:test} Test2() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\0a");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\0a"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\0a"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\0a"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\0a"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\0a"| - i - 1 == 2;
}
method {:test} Test3() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"| - i - 1 == 2;
}

// REPEAT 2 - TIME: 4.3537929 s

method {:test} Test4() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.a\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.a\0"| && "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.a\0"[i] == '.' && |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.a\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.a\0"| && "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.a\0"[i] == '.' && |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.a\0"| - i - 1 == 2;
}
method {:test} Test5() {
var r0 := IsDecimalWithTwoPrecision("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| && "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i] == '.' && |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| && "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i] == '.' && |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| - i - 1 == 2;
}

// REPEAT 3 - TIME: 5.6340614 s

method {:test} Test6() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0"| - i - 1 == 2;
}
method {:test} Test7() {
var r0 := IsDecimalWithTwoPrecision("aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa");
expect r0 ==> exists i :: 0 <= i < |"aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| && "aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"[i] == '.' && |"aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| && "aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"[i] == '.' && |"aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| - i - 1 == 2;
}

// REPEAT 4 - TIME: 7.4545682 s

method {:test} Test8() {
var r0 := IsDecimalWithTwoPrecision("\U{0001}.\U{0003}a");
expect r0 ==> exists i :: 0 <= i < |"\U{0001}.\U{0003}a"| && "\U{0001}.\U{0003}a"[i] == '.' && |"\U{0001}.\U{0003}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0001}.\U{0003}a"| && "\U{0001}.\U{0003}a"[i] == '.' && |"\U{0001}.\U{0003}a"| - i - 1 == 2;
}
method {:test} Test9() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| && "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"[i] == '.' && |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| && "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"[i] == '.' && |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| - i - 1 == 2;
}

// REPEAT 5 - TIME: 9.1169154 s

method {:test} Test10() {
var r0 := IsDecimalWithTwoPrecision(".\U{0001}a");
expect r0 ==> exists i :: 0 <= i < |".\U{0001}a"| && ".\U{0001}a"[i] == '.' && |".\U{0001}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |".\U{0001}a"| && ".\U{0001}a"[i] == '.' && |".\U{0001}a"| - i - 1 == 2;
}
method {:test} Test11() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}\0a\U{0006}\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}\0a\U{0006}\U{0002}"| && "\U{0004}\0a\U{0006}\U{0002}"[i] == '.' && |"\U{0004}\0a\U{0006}\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}\0a\U{0006}\U{0002}"| && "\U{0004}\0a\U{0006}\U{0002}"[i] == '.' && |"\U{0004}\0a\U{0006}\U{0002}"| - i - 1 == 2;
}

// REPEAT 6 - TIME: 10.7891414 s

method {:test} Test12() {
var r0 := IsDecimalWithTwoPrecision("aaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0006}.a\U{0004}");
expect r0 ==> exists i :: 0 <= i < |"aaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0006}.a\U{0004}"| && "aaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0006}.a\U{0004}"[i] == '.' && |"aaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0006}.a\U{0004}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0006}.a\U{0004}"| && "aaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0006}.a\U{0004}"[i] == '.' && |"aaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0006}.a\U{0004}"| - i - 1 == 2;
}
method {:test} Test13() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| && "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"[i] == '.' && |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| && "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"[i] == '.' && |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| - i - 1 == 2;
}

// REPEAT 7 - TIME: 12.0345925 s

method {:test} Test14() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaa\U{0007}aa.\U{0005}\U{0001}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaa\U{0007}aa.\U{0005}\U{0001}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaa\U{0007}aa.\U{0005}\U{0001}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaa\U{0007}aa.\U{0005}\U{0001}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaa\U{0007}aa.\U{0005}\U{0001}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaa\U{0007}aa.\U{0005}\U{0001}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaa\U{0007}aa.\U{0005}\U{0001}"| - i - 1 == 2;
}
method {:test} Test15() {
var r0 := IsDecimalWithTwoPrecision("\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa");
expect r0 ==> exists i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| && "\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"[i] == '.' && |"\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| && "\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"[i] == '.' && |"\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| - i - 1 == 2;
}

// REPEAT 8 - TIME: 13.349977 s

method {:test} Test16() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}aaaaaaa\t\U{000B}aa.\U{0003}\U{0001}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}aaaaaaa\t\U{000B}aa.\U{0003}\U{0001}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}aaaaaaa\t\U{000B}aa.\U{0003}\U{0001}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}aaaaaaa\t\U{000B}aa.\U{0003}\U{0001}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}aaaaaaa\t\U{000B}aa.\U{0003}\U{0001}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}aaaaaaa\t\U{000B}aa.\U{0003}\U{0001}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}aaaaaaa\t\U{000B}aa.\U{0003}\U{0001}"| - i - 1 == 2;
}
method {:test} Test17() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaaaaaaa\U{0004}\U{0006}\na\U{0008}aaaaaaaaaa\0aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaaaaaaa\U{0004}\U{0006}\na\U{0008}aaaaaaaaaa\0aa"| && "\U{0002}aaaaaaaa\U{0004}\U{0006}\na\U{0008}aaaaaaaaaa\0aa"[i] == '.' && |"\U{0002}aaaaaaaa\U{0004}\U{0006}\na\U{0008}aaaaaaaaaa\0aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaaaaaaa\U{0004}\U{0006}\na\U{0008}aaaaaaaaaa\0aa"| && "\U{0002}aaaaaaaa\U{0004}\U{0006}\na\U{0008}aaaaaaaaaa\0aa"[i] == '.' && |"\U{0002}aaaaaaaa\U{0004}\U{0006}\na\U{0008}aaaaaaaaaa\0aa"| - i - 1 == 2;
}

// REPEAT 9 - TIME: 15.0042608 s

method {:test} Test18() {
var r0 := IsDecimalWithTwoPrecision("\U{0007}aaaaaaaaaaaaaaa\U{0001}a\U{0005}aaaaaa\U{0003}.aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0007}aaaaaaaaaaaaaaa\U{0001}a\U{0005}aaaaaa\U{0003}.aa"| && "\U{0007}aaaaaaaaaaaaaaa\U{0001}a\U{0005}aaaaaa\U{0003}.aa"[i] == '.' && |"\U{0007}aaaaaaaaaaaaaaa\U{0001}a\U{0005}aaaaaa\U{0003}.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0007}aaaaaaaaaaaaaaa\U{0001}a\U{0005}aaaaaa\U{0003}.aa"| && "\U{0007}aaaaaaaaaaaaaaa\U{0001}a\U{0005}aaaaaa\U{0003}.aa"[i] == '.' && |"\U{0007}aaaaaaaaaaaaaaa\U{0001}a\U{0005}aaaaaa\U{0003}.aa"| - i - 1 == 2;
}
method {:test} Test19() {
var r0 := IsDecimalWithTwoPrecision("\0\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\0\U{0002}"| && "\0\U{0002}"[i] == '.' && |"\0\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0\U{0002}"| && "\0\U{0002}"[i] == '.' && |"\0\U{0002}"| - i - 1 == 2;
}

// REPEAT 10 - TIME: 16.4640362 s
