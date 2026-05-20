// dafny-synthesis_task_id_602.dfy

method {:testEntry} FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i
  ensures !found ==> forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
{
  c := ' ';
  found := false;
  var inner_found := false;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant found == inner_found
    invariant found ==> exists ii, jj :: 0 <= ii < i && ii < jj < |s| && s[ii] == s[jj] && s[ii] == c && forall k, l :: 0 <= k < l < jj && s[k] == s[l] ==> k >= ii
    invariant !found <==> forall ii, jj :: 0 <= ii < i && ii < jj < |s| ==> s[ii] != s[jj]
  {
    var j := i + 1;
    while j < |s|
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
method {:test} Test10() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}");
expect r0 ==> exists i: int, j: int {:trigger "\U{0002}"[j], "\U{0002}"[i]} :: 0 <= i < j < |"\U{0002}"| && "\U{0002}"[i] == "\U{0002}"[j] && "\U{0002}"[i] == r1 && forall k: int, l: int {:trigger "\U{0002}"[l], "\U{0002}"[k]} :: 0 <= k < l < j && "\U{0002}"[k] == "\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\U{0002}"[j], "\U{0002}"[i]} :: 0 <= i < j < |"\U{0002}"| ==> "\U{0002}"[i] != "\U{0002}"[j];
}
method {:test} Test11() {
var r0, r1 := FindFirstRepeatedChar("a\U{0001}");
expect r0 ==> exists i: int, j: int {:trigger "a\U{0001}"[j], "a\U{0001}"[i]} :: 0 <= i < j < |"a\U{0001}"| && "a\U{0001}"[i] == "a\U{0001}"[j] && "a\U{0001}"[i] == r1 && forall k: int, l: int {:trigger "a\U{0001}"[l], "a\U{0001}"[k]} :: 0 <= k < l < j && "a\U{0001}"[k] == "a\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "a\U{0001}"[j], "a\U{0001}"[i]} :: 0 <= i < j < |"a\U{0001}"| ==> "a\U{0001}"[i] != "a\U{0001}"[j];
}
method {:test} Test12() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0004}");
expect r0 ==> exists i: int, j: int {:trigger "\U{0002}\U{0004}"[j], "\U{0002}\U{0004}"[i]} :: 0 <= i < j < |"\U{0002}\U{0004}"| && "\U{0002}\U{0004}"[i] == "\U{0002}\U{0004}"[j] && "\U{0002}\U{0004}"[i] == r1 && forall k: int, l: int {:trigger "\U{0002}\U{0004}"[l], "\U{0002}\U{0004}"[k]} :: 0 <= k < l < j && "\U{0002}\U{0004}"[k] == "\U{0002}\U{0004}"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\U{0002}\U{0004}"[j], "\U{0002}\U{0004}"[i]} :: 0 <= i < j < |"\U{0002}\U{0004}"| ==> "\U{0002}\U{0004}"[i] != "\U{0002}\U{0004}"[j];
}
method {:test} Test13() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0002}");
expect r0 ==> exists i: int, j: int {:trigger "\U{0002}\U{0002}"[j], "\U{0002}\U{0002}"[i]} :: 0 <= i < j < |"\U{0002}\U{0002}"| && "\U{0002}\U{0002}"[i] == "\U{0002}\U{0002}"[j] && "\U{0002}\U{0002}"[i] == r1 && forall k: int, l: int {:trigger "\U{0002}\U{0002}"[l], "\U{0002}\U{0002}"[k]} :: 0 <= k < l < j && "\U{0002}\U{0002}"[k] == "\U{0002}\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\U{0002}\U{0002}"[j], "\U{0002}\U{0002}"[i]} :: 0 <= i < j < |"\U{0002}\U{0002}"| ==> "\U{0002}\U{0002}"[i] != "\U{0002}\U{0002}"[j];
}
method {:test} Test14() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}");
expect r0 ==> exists i: int, j: int {:trigger "\U{0002}"[j], "\U{0002}"[i]} :: 0 <= i < j < |"\U{0002}"| && "\U{0002}"[i] == "\U{0002}"[j] && "\U{0002}"[i] == r1 && forall k: int, l: int {:trigger "\U{0002}"[l], "\U{0002}"[k]} :: 0 <= k < l < j && "\U{0002}"[k] == "\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\U{0002}"[j], "\U{0002}"[i]} :: 0 <= i < j < |"\U{0002}"| ==> "\U{0002}"[i] != "\U{0002}"[j];
}
method {:test} Test15() {
var r0, r1 := FindFirstRepeatedChar("aa\U{0001}");
expect r0 ==> exists i: int, j: int {:trigger "aa\U{0001}"[j], "aa\U{0001}"[i]} :: 0 <= i < j < |"aa\U{0001}"| && "aa\U{0001}"[i] == "aa\U{0001}"[j] && "aa\U{0001}"[i] == r1 && forall k: int, l: int {:trigger "aa\U{0001}"[l], "aa\U{0001}"[k]} :: 0 <= k < l < j && "aa\U{0001}"[k] == "aa\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "aa\U{0001}"[j], "aa\U{0001}"[i]} :: 0 <= i < j < |"aa\U{0001}"| ==> "aa\U{0001}"[i] != "aa\U{0001}"[j];
}
method {:test} Test16() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0002}");
expect r0 ==> exists i: int, j: int {:trigger "\U{0002}\U{0002}"[j], "\U{0002}\U{0002}"[i]} :: 0 <= i < j < |"\U{0002}\U{0002}"| && "\U{0002}\U{0002}"[i] == "\U{0002}\U{0002}"[j] && "\U{0002}\U{0002}"[i] == r1 && forall k: int, l: int {:trigger "\U{0002}\U{0002}"[l], "\U{0002}\U{0002}"[k]} :: 0 <= k < l < j && "\U{0002}\U{0002}"[k] == "\U{0002}\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\U{0002}\U{0002}"[j], "\U{0002}\U{0002}"[i]} :: 0 <= i < j < |"\U{0002}\U{0002}"| ==> "\U{0002}\U{0002}"[i] != "\U{0002}\U{0002}"[j];
}
method {:test} Test17() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}");
expect r0 ==> exists i: int, j: int {:trigger "\U{0002}"[j], "\U{0002}"[i]} :: 0 <= i < j < |"\U{0002}"| && "\U{0002}"[i] == "\U{0002}"[j] && "\U{0002}"[i] == r1 && forall k: int, l: int {:trigger "\U{0002}"[l], "\U{0002}"[k]} :: 0 <= k < l < j && "\U{0002}"[k] == "\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\U{0002}"[j], "\U{0002}"[i]} :: 0 <= i < j < |"\U{0002}"| ==> "\U{0002}"[i] != "\U{0002}"[j];
}
method {:test} Test18() {
var r0, r1 := FindFirstRepeatedChar("aa\U{0001}a");
expect r0 ==> exists i: int, j: int {:trigger "aa\U{0001}a"[j], "aa\U{0001}a"[i]} :: 0 <= i < j < |"aa\U{0001}a"| && "aa\U{0001}a"[i] == "aa\U{0001}a"[j] && "aa\U{0001}a"[i] == r1 && forall k: int, l: int {:trigger "aa\U{0001}a"[l], "aa\U{0001}a"[k]} :: 0 <= k < l < j && "aa\U{0001}a"[k] == "aa\U{0001}a"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "aa\U{0001}a"[j], "aa\U{0001}a"[i]} :: 0 <= i < j < |"aa\U{0001}a"| ==> "aa\U{0001}a"[i] != "aa\U{0001}a"[j];
}
method {:test} Test19() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0002}");
expect r0 ==> exists i: int, j: int {:trigger "\U{0002}\U{0002}"[j], "\U{0002}\U{0002}"[i]} :: 0 <= i < j < |"\U{0002}\U{0002}"| && "\U{0002}\U{0002}"[i] == "\U{0002}\U{0002}"[j] && "\U{0002}\U{0002}"[i] == r1 && forall k: int, l: int {:trigger "\U{0002}\U{0002}"[l], "\U{0002}\U{0002}"[k]} :: 0 <= k < l < j && "\U{0002}\U{0002}"[k] == "\U{0002}\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\U{0002}\U{0002}"[j], "\U{0002}\U{0002}"[i]} :: 0 <= i < j < |"\U{0002}\U{0002}"| ==> "\U{0002}\U{0002}"[i] != "\U{0002}\U{0002}"[j];
}
method {:test} Test20() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}");
expect r0 ==> exists i: int, j: int {:trigger "\U{0002}"[j], "\U{0002}"[i]} :: 0 <= i < j < |"\U{0002}"| && "\U{0002}"[i] == "\U{0002}"[j] && "\U{0002}"[i] == r1 && forall k: int, l: int {:trigger "\U{0002}"[l], "\U{0002}"[k]} :: 0 <= k < l < j && "\U{0002}"[k] == "\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\U{0002}"[j], "\U{0002}"[i]} :: 0 <= i < j < |"\U{0002}"| ==> "\U{0002}"[i] != "\U{0002}"[j];
}
method {:test} Test21() {
var r0, r1 := FindFirstRepeatedChar("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}");
expect r0 ==> exists i: int, j: int {:trigger "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[j], "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]} :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[j] && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] == r1 && forall k: int, l: int {:trigger "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[l], "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[k]} :: 0 <= k < l < j && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[k] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[j], "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]} :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] != "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[j];
}
method {:test} Test22() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0004}");
expect r0 ==> exists i: int, j: int {:trigger "\U{0002}\U{0004}"[j], "\U{0002}\U{0004}"[i]} :: 0 <= i < j < |"\U{0002}\U{0004}"| && "\U{0002}\U{0004}"[i] == "\U{0002}\U{0004}"[j] && "\U{0002}\U{0004}"[i] == r1 && forall k: int, l: int {:trigger "\U{0002}\U{0004}"[l], "\U{0002}\U{0004}"[k]} :: 0 <= k < l < j && "\U{0002}\U{0004}"[k] == "\U{0002}\U{0004}"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\U{0002}\U{0004}"[j], "\U{0002}\U{0004}"[i]} :: 0 <= i < j < |"\U{0002}\U{0004}"| ==> "\U{0002}\U{0004}"[i] != "\U{0002}\U{0004}"[j];
}
method {:test} Test23() {
var r0, r1 := FindFirstRepeatedChar("\U{0002}\U{0002}aaa");
expect r0 ==> exists i: int, j: int {:trigger "\U{0002}\U{0002}aaa"[j], "\U{0002}\U{0002}aaa"[i]} :: 0 <= i < j < |"\U{0002}\U{0002}aaa"| && "\U{0002}\U{0002}aaa"[i] == "\U{0002}\U{0002}aaa"[j] && "\U{0002}\U{0002}aaa"[i] == r1 && forall k: int, l: int {:trigger "\U{0002}\U{0002}aaa"[l], "\U{0002}\U{0002}aaa"[k]} :: 0 <= k < l < j && "\U{0002}\U{0002}aaa"[k] == "\U{0002}\U{0002}aaa"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\U{0002}\U{0002}aaa"[j], "\U{0002}\U{0002}aaa"[i]} :: 0 <= i < j < |"\U{0002}\U{0002}aaa"| ==> "\U{0002}\U{0002}aaa"[i] != "\U{0002}\U{0002}aaa"[j];
}
