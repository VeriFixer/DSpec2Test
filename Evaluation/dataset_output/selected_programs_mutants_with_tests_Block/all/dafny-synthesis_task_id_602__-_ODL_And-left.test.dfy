// dafny-synthesis_task_id_602.dfy

method {:testEntry} FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i
  ensures !found ==> forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
{
  c := ' ';
  found := false;
  var inner_found := false;
  var i := 0;
  while !found
    invariant 0 <= i <= |s|
    invariant found == inner_found
    invariant found ==> exists ii, jj :: 0 <= ii < i && ii < jj < |s| && s[ii] == s[jj] && s[ii] == c && forall k, l :: 0 <= k < l < jj && s[k] == s[l] ==> k >= ii
    invariant !found <==> forall ii, jj :: 0 <= ii < i && ii < jj < |s| ==> s[ii] != s[jj]
  {
    var j := i + 1;
    while !inner_found
      invariant i < j <= |s|
      invariant inner_found ==> exists k :: i < k < |s| && s[i] == s[k] && s[i] == c
      invariant !inner_found <==> forall k :: i < k < j ==> s[i] != s[k]
    {
      if s[i] == s[j] {
        inner_found := true;
        c := s[i];
      }
      j := j + 1;
    }
    found := inner_found;
    i := i + 1;
  }
}


method {:test} Test0() {
var r0, r1 := FindFirstRepeatedChar("");
expect r0 ==> exists i, j :: 0 <= i < j < |""| && ""[i] == ""[j] && ""[i] == r1 && forall k, l :: 0 <= k < l < j && ""[k] == ""[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |""| ==> ""[i] != ""[j];
}
method {:test} Test1() {
var r0, r1 := FindFirstRepeatedChar("a");
expect r0 ==> exists i, j :: 0 <= i < j < |"a"| && "a"[i] == "a"[j] && "a"[i] == r1 && forall k, l :: 0 <= k < l < j && "a"[k] == "a"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"a"| ==> "a"[i] != "a"[j];
}

// REPEAT 1 - TIME: 7.1804942 s

method {:test} Test10() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}"| && "\U{0002}"[i] == "\U{0002}"[j] && "\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}"[k] == "\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}"| ==> "\U{0002}"[i] != "\U{0002}"[j];
}
method {:test} Test11() {
var r0, r1 := FindFirstRepeatedChar("aa");
expect r0 ==> exists i, j :: 0 <= i < j < |"aa"| && "aa"[i] == "aa"[j] && "aa"[i] == r1 && forall k, l :: 0 <= k < l < j && "aa"[k] == "aa"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aa"| ==> "aa"[i] != "aa"[j];
}
method {:test} Test12() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0004}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0004}"| && "\U{0002}\U{0004}"[i] == "\U{0002}\U{0004}"[j] && "\U{0002}\U{0004}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0004}"[k] == "\U{0002}\U{0004}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0004}"| ==> "\U{0002}\U{0004}"[i] != "\U{0002}\U{0004}"[j];
}
method {:test} Test13() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0002}"| && "\U{0002}\U{0002}"[i] == "\U{0002}\U{0002}"[j] && "\U{0002}\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0002}"[k] == "\U{0002}\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0002}"| ==> "\U{0002}\U{0002}"[i] != "\U{0002}\U{0002}"[j];
}

// REPEAT 2 - TIME: 9.3246402 s

method {:test} Test14() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}"| && "\U{0002}"[i] == "\U{0002}"[j] && "\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}"[k] == "\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}"| ==> "\U{0002}"[i] != "\U{0002}"[j];
}
method {:test} Test15() {
var r0, r1 := FindFirstRepeatedChar("a\U{0001}a");
expect r0 ==> exists i, j :: 0 <= i < j < |"a\U{0001}a"| && "a\U{0001}a"[i] == "a\U{0001}a"[j] && "a\U{0001}a"[i] == r1 && forall k, l :: 0 <= k < l < j && "a\U{0001}a"[k] == "a\U{0001}a"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"a\U{0001}a"| ==> "a\U{0001}a"[i] != "a\U{0001}a"[j];
}
method {:test} Test16() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0002}"| && "\U{0002}\U{0002}"[i] == "\U{0002}\U{0002}"[j] && "\U{0002}\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0002}"[k] == "\U{0002}\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0002}"| ==> "\U{0002}\U{0002}"[i] != "\U{0002}\U{0002}"[j];
}

// REPEAT 3 - TIME: 10.9697752 s

method {:test} Test17() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}"| && "\U{0002}"[i] == "\U{0002}"[j] && "\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}"[k] == "\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}"| ==> "\U{0002}"[i] != "\U{0002}"[j];
}
method {:test} Test18() {
var r0, r1 := FindFirstRepeatedChar("a\U{0001}aa");
expect r0 ==> exists i, j :: 0 <= i < j < |"a\U{0001}aa"| && "a\U{0001}aa"[i] == "a\U{0001}aa"[j] && "a\U{0001}aa"[i] == r1 && forall k, l :: 0 <= k < l < j && "a\U{0001}aa"[k] == "a\U{0001}aa"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"a\U{0001}aa"| ==> "a\U{0001}aa"[i] != "a\U{0001}aa"[j];
}
method {:test} Test19() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0002}"| && "\U{0002}\U{0002}"[i] == "\U{0002}\U{0002}"[j] && "\U{0002}\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0002}"[k] == "\U{0002}\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0002}"| ==> "\U{0002}\U{0002}"[i] != "\U{0002}\U{0002}"[j];
}

// REPEAT 4 - TIME: 12.641666 s

method {:test} Test20() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}"| && "\U{0002}"[i] == "\U{0002}"[j] && "\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}"[k] == "\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}"| ==> "\U{0002}"[i] != "\U{0002}"[j];
}
method {:test} Test21() {
var r0, r1 := FindFirstRepeatedChar("aaaaa");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaa"| && "aaaaa"[i] == "aaaaa"[j] && "aaaaa"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaa"[k] == "aaaaa"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaa"| ==> "aaaaa"[i] != "aaaaa"[j];
}
method {:test} Test22() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0002}"| && "\U{0002}\U{0002}"[i] == "\U{0002}\U{0002}"[j] && "\U{0002}\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0002}"[k] == "\U{0002}\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0002}"| ==> "\U{0002}\U{0002}"[i] != "\U{0002}\U{0002}"[j];
}

// REPEAT 5 - TIME: 14.1653966 s

method {:test} Test23() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}"| && "\U{0002}"[i] == "\U{0002}"[j] && "\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}"[k] == "\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}"| ==> "\U{0002}"[i] != "\U{0002}"[j];
}
method {:test} Test24() {
var r0, r1 := FindFirstRepeatedChar("aaaaa\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaa\U{0001}"| && "aaaaa\U{0001}"[i] == "aaaaa\U{0001}"[j] && "aaaaa\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaa\U{0001}"[k] == "aaaaa\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaa\U{0001}"| ==> "aaaaa\U{0001}"[i] != "aaaaa\U{0001}"[j];
}
method {:test} Test25() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0002}"| && "\U{0002}\U{0002}"[i] == "\U{0002}\U{0002}"[j] && "\U{0002}\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0002}"[k] == "\U{0002}\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0002}"| ==> "\U{0002}\U{0002}"[i] != "\U{0002}\U{0002}"[j];
}

// REPEAT 6 - TIME: 15.5816717 s

method {:test} Test26() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}"| && "\U{0002}"[i] == "\U{0002}"[j] && "\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}"[k] == "\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}"| ==> "\U{0002}"[i] != "\U{0002}"[j];
}
method {:test} Test27() {
var r0, r1 := FindFirstRepeatedChar("aaaaa\U{0001}a");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaa\U{0001}a"| && "aaaaa\U{0001}a"[i] == "aaaaa\U{0001}a"[j] && "aaaaa\U{0001}a"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaa\U{0001}a"[k] == "aaaaa\U{0001}a"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaa\U{0001}a"| ==> "aaaaa\U{0001}a"[i] != "aaaaa\U{0001}a"[j];
}
method {:test} Test28() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0004}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0004}"| && "\U{0002}\U{0004}"[i] == "\U{0002}\U{0004}"[j] && "\U{0002}\U{0004}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0004}"[k] == "\U{0002}\U{0004}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0004}"| ==> "\U{0002}\U{0004}"[i] != "\U{0002}\U{0004}"[j];
}
method {:test} Test29() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0002}aaa\U{0003}a");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0002}aaa\U{0003}a"| && "\U{0002}\U{0002}aaa\U{0003}a"[i] == "\U{0002}\U{0002}aaa\U{0003}a"[j] && "\U{0002}\U{0002}aaa\U{0003}a"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0002}aaa\U{0003}a"[k] == "\U{0002}\U{0002}aaa\U{0003}a"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0002}aaa\U{0003}a"| ==> "\U{0002}\U{0002}aaa\U{0003}a"[i] != "\U{0002}\U{0002}aaa\U{0003}a"[j];
}

// REPEAT 7 - TIME: 17.1999231 s

method {:test} Test30() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}"| && "\U{0002}"[i] == "\U{0002}"[j] && "\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}"[k] == "\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}"| ==> "\U{0002}"[i] != "\U{0002}"[j];
}
method {:test} Test31() {
var r0, r1 := FindFirstRepeatedChar("aaaaa\U{0001}aa");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaa\U{0001}aa"| && "aaaaa\U{0001}aa"[i] == "aaaaa\U{0001}aa"[j] && "aaaaa\U{0001}aa"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaa\U{0001}aa"[k] == "aaaaa\U{0001}aa"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaa\U{0001}aa"| ==> "aaaaa\U{0001}aa"[i] != "aaaaa\U{0001}aa"[j];
}
method {:test} Test32() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0004}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0004}"| && "\U{0002}\U{0004}"[i] == "\U{0002}\U{0004}"[j] && "\U{0002}\U{0004}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0004}"[k] == "\U{0002}\U{0004}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0004}"| ==> "\U{0002}\U{0004}"[i] != "\U{0002}\U{0004}"[j];
}
method {:test} Test33() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0002}aaa\U{0003}aa");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0002}aaa\U{0003}aa"| && "\U{0002}\U{0002}aaa\U{0003}aa"[i] == "\U{0002}\U{0002}aaa\U{0003}aa"[j] && "\U{0002}\U{0002}aaa\U{0003}aa"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0002}aaa\U{0003}aa"[k] == "\U{0002}\U{0002}aaa\U{0003}aa"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0002}aaa\U{0003}aa"| ==> "\U{0002}\U{0002}aaa\U{0003}aa"[i] != "\U{0002}\U{0002}aaa\U{0003}aa"[j];
}

// REPEAT 8 - TIME: 19.2609079 s

method {:test} Test34() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}"| && "\U{0002}"[i] == "\U{0002}"[j] && "\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}"[k] == "\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}"| ==> "\U{0002}"[i] != "\U{0002}"[j];
}
method {:test} Test35() {
var r0, r1 := FindFirstRepeatedChar("aaaaaaaaa");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaaaaaa"| && "aaaaaaaaa"[i] == "aaaaaaaaa"[j] && "aaaaaaaaa"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaaaaaa"[k] == "aaaaaaaaa"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaaaaaa"| ==> "aaaaaaaaa"[i] != "aaaaaaaaa"[j];
}
method {:test} Test36() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0002}"| && "\U{0002}\U{0002}"[i] == "\U{0002}\U{0002}"[j] && "\U{0002}\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0002}"[k] == "\U{0002}\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0002}"| ==> "\U{0002}\U{0002}"[i] != "\U{0002}\U{0002}"[j];
}

// REPEAT 9 - TIME: 20.6586336 s

method {:test} Test37() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}"| && "\U{0002}"[i] == "\U{0002}"[j] && "\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}"[k] == "\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}"| ==> "\U{0002}"[i] != "\U{0002}"[j];
}
method {:test} Test38() {
var r0, r1 := FindFirstRepeatedChar("aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[j] && "aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[k] == "aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] != "aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[j];
}
method {:test} Test39() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0004}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0004}"| && "\U{0002}\U{0004}"[i] == "\U{0002}\U{0004}"[j] && "\U{0002}\U{0004}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0004}"[k] == "\U{0002}\U{0004}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0004}"| ==> "\U{0002}\U{0004}"[i] != "\U{0002}\U{0004}"[j];
}
method {:test} Test40() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0002}aaaaaaaa");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0002}aaaaaaaa"| && "\U{0002}\U{0002}aaaaaaaa"[i] == "\U{0002}\U{0002}aaaaaaaa"[j] && "\U{0002}\U{0002}aaaaaaaa"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0002}aaaaaaaa"[k] == "\U{0002}\U{0002}aaaaaaaa"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0002}aaaaaaaa"| ==> "\U{0002}\U{0002}aaaaaaaa"[i] != "\U{0002}\U{0002}aaaaaaaa"[j];
}

// REPEAT 10 - TIME: 22.5022992 s
