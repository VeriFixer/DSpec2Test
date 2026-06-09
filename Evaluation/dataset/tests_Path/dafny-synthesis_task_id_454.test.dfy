method {:testEntry} ContainsZ(s: string) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z'))
{
    result := false;
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant result <==> (exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z'))
    {
        if s[i] == 'z' || s[i] == 'Z' {
            result := true;
            break;
        }
    }
}

method {:test} Test0() {
var r0 := ContainsZ("a");
expect r0 <==> exists i :: 0 <= i < |"a"| && ("a"[i] == 'z' || "a"[i] == 'Z');
}
method {:test} Test1() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"[i] == 'Z');
}

// REPEAT 1 - TIME: 14.431867 s

method {:test} Test3() {
var r0 := ContainsZ("\0a");
expect r0 <==> exists i :: 0 <= i < |"\0a"| && ("\0a"[i] == 'z' || "\0a"[i] == 'Z');
}
method {:test} Test4() {
var r0 := ContainsZ("\U{0003}\U{0001}Z");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}\U{0001}Z"| && ("\U{0003}\U{0001}Z"[i] == 'z' || "\U{0003}\U{0001}Z"[i] == 'Z');
}
method {:test} Test5() {
var r0 := ContainsZ("Z\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"Z\U{0001}"| && ("Z\U{0001}"[i] == 'z' || "Z\U{0001}"[i] == 'Z');
}

// REPEAT 2 - TIME: 41.8063389 s

method {:test} Test6() {
var r0 := ContainsZ("\U{0002}\0");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}\0"| && ("\U{0002}\0"[i] == 'z' || "\U{0002}\0"[i] == 'Z');
}
method {:test} Test7() {
var r0 := ContainsZ("\U{0002}Z\U{0004}aaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}Z\U{0004}aaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0006}"| && ("\U{0002}Z\U{0004}aaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0006}"[i] == 'z' || "\U{0002}Z\U{0004}aaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0006}"[i] == 'Z');
}
method {:test} Test8() {
var r0 := ContainsZ("Za\U{0004}aaaa\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"Za\U{0004}aaaa\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0006}"| && ("Za\U{0004}aaaa\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0006}"[i] == 'z' || "Za\U{0004}aaaa\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0006}"[i] == 'Z');
}

// REPEAT 3 - TIME: 76.3272832 s

method {:test} Test9() {
var r0 := ContainsZ("\0aa");
expect r0 <==> exists i :: 0 <= i < |"\0aa"| && ("\0aa"[i] == 'z' || "\0aa"[i] == 'Z');
}
method {:test} Test10() {
var r0 := ContainsZ("\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}az\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}az\U{0001}"| && ("\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}az\U{0001}"[i] == 'z' || "\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}az\U{0001}"[i] == 'Z');
}

// REPEAT 4 - TIME: 123.0037761 s

method {:test} Test12() {
var r0 := ContainsZ("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\U{0006}"| && ("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\U{0006}"[i] == 'z' || "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\U{0006}"[i] == 'Z');
}
method {:test} Test13() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}Z");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}Z"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}Z"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}Z"[i] == 'Z');
}

// REPEAT 5 - TIME: 190.0620177 s

method {:test} Test15() {
var r0 := ContainsZ("\U{0006}aaaaaaaaaaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaa\U{0008}a\na\U{0004}aaaa\U{000C}");
expect r0 <==> exists i :: 0 <= i < |"\U{0006}aaaaaaaaaaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaa\U{0008}a\na\U{0004}aaaa\U{000C}"| && ("\U{0006}aaaaaaaaaaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaa\U{0008}a\na\U{0004}aaaa\U{000C}"[i] == 'z' || "\U{0006}aaaaaaaaaaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaa\U{0008}a\na\U{0004}aaaa\U{000C}"[i] == 'Z');
}
method {:test} Test16() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz"[i] == 'Z');
}
method {:test} Test17() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}Z");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}Z"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}Z"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}Z"[i] == 'Z');
}

// REPEAT 6 - TIME: 276.0127737 s

method {:test} Test18() {
var r0 := ContainsZ("\U{000C}a\U{0004}aaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}\U{0008}\n");
expect r0 <==> exists i :: 0 <= i < |"\U{000C}a\U{0004}aaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}\U{0008}\n"| && ("\U{000C}a\U{0004}aaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}\U{0008}\n"[i] == 'z' || "\U{000C}a\U{0004}aaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}\U{0008}\n"[i] == 'Z');
}
method {:test} Test19() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"[i] == 'Z');
}
method {:test} Test20() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\U{0001}"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\U{0001}"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\U{0001}"[i] == 'Z');
}

// REPEAT 7 - TIME: 374.939978 s

method {:test} Test21() {
var r0 := ContainsZ("aaa\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}\U{0006}aaa\U{0004}a");
expect r0 <==> exists i :: 0 <= i < |"aaa\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}\U{0006}aaa\U{0004}a"| && ("aaa\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}\U{0006}aaa\U{0004}a"[i] == 'z' || "aaa\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}\U{0006}aaa\U{0004}a"[i] == 'Z');
}
method {:test} Test22() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZaaaaaaaa");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZaaaaaaaa"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZaaaaaaaa"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZaaaaaaaa"[i] == 'Z');
}

// REPEAT 8 - TIME: 474.5693697 s

method {:test} Test24() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}aaaaa");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}aaaaa"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}aaaaa"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}aaaaa"[i] == 'Z');
}
method {:test} Test25() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"[i] == 'Z');
}

// REPEAT 9 - TIME: 587.3119209 s

method {:test} Test27() {
var r0 := ContainsZ("\n\U{0008}\U{0006}a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"\n\U{0008}\U{0006}a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}"| && ("\n\U{0008}\U{0006}a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}"[i] == 'z' || "\n\U{0008}\U{0006}a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}"[i] == 'Z');
}
method {:test} Test28() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"[i] == 'Z');
}

// REPEAT 10 - TIME: 723.6160778 s
