// dafny-synthesis_task_id_602.dfy

method {:testEntry} FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i
  ensures !found ==> forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
{
  c := ' ';
  found := false;
  var inner_found := false;
  var i := 0;
  while i < |s| ==> !found
    invariant 0 <= i <= |s|
    invariant found == inner_found
    invariant found ==> exists ii, jj :: 0 <= ii < i && ii < jj < |s| && s[ii] == s[jj] && s[ii] == c && forall k, l :: 0 <= k < l < jj && s[k] == s[l] ==> k >= ii
    invariant !found <==> forall ii, jj :: 0 <= ii < i && ii < jj < |s| ==> s[ii] != s[jj]
  {
    var j := i + 1;
    while j < |s| && !inner_found
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

// REPEAT 1 - TIME: 7.33691 s

method {:test} Test10() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}"| && "\U{0002}"[i] == "\U{0002}"[j] && "\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}"[k] == "\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}"| ==> "\U{0002}"[i] != "\U{0002}"[j];
}
method {:test} Test11() {
var r0, r1 := FindFirstRepeatedChar("a\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"a\U{0001}"| && "a\U{0001}"[i] == "a\U{0001}"[j] && "a\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "a\U{0001}"[k] == "a\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"a\U{0001}"| ==> "a\U{0001}"[i] != "a\U{0001}"[j];
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

// REPEAT 2 - TIME: 9.2023284 s

method {:test} Test14() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}"| && "\U{0002}"[i] == "\U{0002}"[j] && "\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}"[k] == "\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}"| ==> "\U{0002}"[i] != "\U{0002}"[j];
}
method {:test} Test15() {
var r0, r1 := FindFirstRepeatedChar("aaa");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaa"| && "aaa"[i] == "aaa"[j] && "aaa"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaa"[k] == "aaa"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaa"| ==> "aaa"[i] != "aaa"[j];
}
method {:test} Test16() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0002}"| && "\U{0002}\U{0002}"[i] == "\U{0002}\U{0002}"[j] && "\U{0002}\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0002}"[k] == "\U{0002}\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0002}"| ==> "\U{0002}\U{0002}"[i] != "\U{0002}\U{0002}"[j];
}

// REPEAT 3 - TIME: 10.548405 s

method {:test} Test17() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}"| && "\U{0002}"[i] == "\U{0002}"[j] && "\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}"[k] == "\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}"| ==> "\U{0002}"[i] != "\U{0002}"[j];
}
method {:test} Test18() {
var r0, r1 := FindFirstRepeatedChar("aaaa");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaa"| && "aaaa"[i] == "aaaa"[j] && "aaaa"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaa"[k] == "aaaa"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaa"| ==> "aaaa"[i] != "aaaa"[j];
}
method {:test} Test19() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0002}"| && "\U{0002}\U{0002}"[i] == "\U{0002}\U{0002}"[j] && "\U{0002}\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0002}"[k] == "\U{0002}\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0002}"| ==> "\U{0002}\U{0002}"[i] != "\U{0002}\U{0002}"[j];
}

// REPEAT 4 - TIME: 12.0819755 s

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
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0004}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0004}"| && "\U{0002}\U{0004}"[i] == "\U{0002}\U{0004}"[j] && "\U{0002}\U{0004}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0004}"[k] == "\U{0002}\U{0004}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0004}"| ==> "\U{0002}\U{0004}"[i] != "\U{0002}\U{0004}"[j];
}
method {:test} Test23() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0002}aaa");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0002}aaa"| && "\U{0002}\U{0002}aaa"[i] == "\U{0002}\U{0002}aaa"[j] && "\U{0002}\U{0002}aaa"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0002}aaa"[k] == "\U{0002}\U{0002}aaa"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0002}aaa"| ==> "\U{0002}\U{0002}aaa"[i] != "\U{0002}\U{0002}aaa"[j];
}

// REPEAT 5 - TIME: 14.048216 s

method {:test} Test24() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}"| && "\U{0002}"[i] == "\U{0002}"[j] && "\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}"[k] == "\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}"| ==> "\U{0002}"[i] != "\U{0002}"[j];
}
method {:test} Test25() {
var r0, r1 := FindFirstRepeatedChar("aaaaaa");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaaa"| && "aaaaaa"[i] == "aaaaaa"[j] && "aaaaaa"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaaa"[k] == "aaaaaa"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaaa"| ==> "aaaaaa"[i] != "aaaaaa"[j];
}
method {:test} Test26() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0002}"| && "\U{0002}\U{0002}"[i] == "\U{0002}\U{0002}"[j] && "\U{0002}\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0002}"[k] == "\U{0002}\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0002}"| ==> "\U{0002}\U{0002}"[i] != "\U{0002}\U{0002}"[j];
}

// REPEAT 6 - TIME: 15.7431583 s

method {:test} Test27() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}"| && "\U{0002}"[i] == "\U{0002}"[j] && "\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}"[k] == "\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}"| ==> "\U{0002}"[i] != "\U{0002}"[j];
}
method {:test} Test28() {
var r0, r1 := FindFirstRepeatedChar("aaaaaaa");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaaaa"| && "aaaaaaa"[i] == "aaaaaaa"[j] && "aaaaaaa"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaaaa"[k] == "aaaaaaa"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaaaa"| ==> "aaaaaaa"[i] != "aaaaaaa"[j];
}
method {:test} Test29() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0004}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0004}"| && "\U{0002}\U{0004}"[i] == "\U{0002}\U{0004}"[j] && "\U{0002}\U{0004}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0004}"[k] == "\U{0002}\U{0004}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0004}"| ==> "\U{0002}\U{0004}"[i] != "\U{0002}\U{0004}"[j];
}
method {:test} Test30() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0002}aaaaa");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0002}aaaaa"| && "\U{0002}\U{0002}aaaaa"[i] == "\U{0002}\U{0002}aaaaa"[j] && "\U{0002}\U{0002}aaaaa"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0002}aaaaa"[k] == "\U{0002}\U{0002}aaaaa"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0002}aaaaa"| ==> "\U{0002}\U{0002}aaaaa"[i] != "\U{0002}\U{0002}aaaaa"[j];
}

// REPEAT 7 - TIME: 17.3925532 s

method {:test} Test31() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}"| && "\U{0002}"[i] == "\U{0002}"[j] && "\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}"[k] == "\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}"| ==> "\U{0002}"[i] != "\U{0002}"[j];
}
method {:test} Test32() {
var r0, r1 := FindFirstRepeatedChar("aaaaaaaa");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaaaaa"| && "aaaaaaaa"[i] == "aaaaaaaa"[j] && "aaaaaaaa"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaaaaa"[k] == "aaaaaaaa"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaaaaa"| ==> "aaaaaaaa"[i] != "aaaaaaaa"[j];
}
method {:test} Test33() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0004}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0004}"| && "\U{0002}\U{0004}"[i] == "\U{0002}\U{0004}"[j] && "\U{0002}\U{0004}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0004}"[k] == "\U{0002}\U{0004}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0004}"| ==> "\U{0002}\U{0004}"[i] != "\U{0002}\U{0004}"[j];
}
method {:test} Test34() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0002}aaaaaa");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0002}aaaaaa"| && "\U{0002}\U{0002}aaaaaa"[i] == "\U{0002}\U{0002}aaaaaa"[j] && "\U{0002}\U{0002}aaaaaa"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0002}aaaaaa"[k] == "\U{0002}\U{0002}aaaaaa"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0002}aaaaaa"| ==> "\U{0002}\U{0002}aaaaaa"[i] != "\U{0002}\U{0002}aaaaaa"[j];
}

// REPEAT 8 - TIME: 19.3055326 s

method {:test} Test35() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}"| && "\U{0002}"[i] == "\U{0002}"[j] && "\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}"[k] == "\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}"| ==> "\U{0002}"[i] != "\U{0002}"[j];
}
method {:test} Test36() {
var r0, r1 := FindFirstRepeatedChar("aaaaaaaaa");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaaaaaa"| && "aaaaaaaaa"[i] == "aaaaaaaaa"[j] && "aaaaaaaaa"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaaaaaa"[k] == "aaaaaaaaa"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaaaaaa"| ==> "aaaaaaaaa"[i] != "aaaaaaaaa"[j];
}
method {:test} Test37() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0004}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0004}"| && "\U{0002}\U{0004}"[i] == "\U{0002}\U{0004}"[j] && "\U{0002}\U{0004}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0004}"[k] == "\U{0002}\U{0004}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0004}"| ==> "\U{0002}\U{0004}"[i] != "\U{0002}\U{0004}"[j];
}
method {:test} Test38() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0002}aaaaaaa");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0002}aaaaaaa"| && "\U{0002}\U{0002}aaaaaaa"[i] == "\U{0002}\U{0002}aaaaaaa"[j] && "\U{0002}\U{0002}aaaaaaa"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0002}aaaaaaa"[k] == "\U{0002}\U{0002}aaaaaaa"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0002}aaaaaaa"| ==> "\U{0002}\U{0002}aaaaaaa"[i] != "\U{0002}\U{0002}aaaaaaa"[j];
}

// REPEAT 9 - TIME: 21.0128888 s

method {:test} Test39() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}"| && "\U{0002}"[i] == "\U{0002}"[j] && "\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}"[k] == "\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}"| ==> "\U{0002}"[i] != "\U{0002}"[j];
}
method {:test} Test40() {
var r0, r1 := FindFirstRepeatedChar("aaaaaaaaa\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaaaaaa\U{0001}"| && "aaaaaaaaa\U{0001}"[i] == "aaaaaaaaa\U{0001}"[j] && "aaaaaaaaa\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaaaaaa\U{0001}"[k] == "aaaaaaaaa\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaaaaaa\U{0001}"| ==> "aaaaaaaaa\U{0001}"[i] != "aaaaaaaaa\U{0001}"[j];
}
method {:test} Test41() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0002}\U{0002}"| && "\U{0002}\U{0002}"[i] == "\U{0002}\U{0002}"[j] && "\U{0002}\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0002}\U{0002}"[k] == "\U{0002}\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0002}\U{0002}"| ==> "\U{0002}\U{0002}"[i] != "\U{0002}\U{0002}"[j];
}

// REPEAT 10 - TIME: 22.3318586 s
