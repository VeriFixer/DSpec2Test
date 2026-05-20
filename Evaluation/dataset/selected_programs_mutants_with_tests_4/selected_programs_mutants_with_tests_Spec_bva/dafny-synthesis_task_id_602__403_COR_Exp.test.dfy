// dafny-synthesis_task_id_602.dfy

method {:testEntry} FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i
  ensures !found ==> forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
{
  c := ' ';
  found := false;
  var inner_found := false;
  var i := 0;
  while i < |s| <== !found
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
method {:test} Test2() {
var r0, r1 := FindFirstRepeatedChar("a");
expect r0 ==> exists i, j :: 0 <= i < j < |"a"| && "a"[i] == "a"[j] && "a"[i] == r1 && forall k, l :: 0 <= k < l < j && "a"[k] == "a"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"a"| ==> "a"[i] != "a"[j];
}
method {:test} Test3() {
var r0, r1 := FindFirstRepeatedChar("aa");
expect r0 ==> exists i, j :: 0 <= i < j < |"aa"| && "aa"[i] == "aa"[j] && "aa"[i] == r1 && forall k, l :: 0 <= k < l < j && "aa"[k] == "aa"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aa"| ==> "aa"[i] != "aa"[j];
}
method {:test} Test9() {
var r0, r1 := FindFirstRepeatedChar("aaaaaaaaaaaaaaaaaaaaaa\0\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaaaa\0\0"| && "aaaaaaaaaaaaaaaaaaaaaa\0\0"[i] == "aaaaaaaaaaaaaaaaaaaaaa\0\0"[j] && "aaaaaaaaaaaaaaaaaaaaaa\0\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaaaaaaaaaaaaaaaaaaa\0\0"[k] == "aaaaaaaaaaaaaaaaaaaaaa\0\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaaaa\0\0"| ==> "aaaaaaaaaaaaaaaaaaaaaa\0\0"[i] != "aaaaaaaaaaaaaaaaaaaaaa\0\0"[j];
}
method {:test} Test10() {
var r0, r1 := FindFirstRepeatedChar("aaaaaaaaaaaaaaaaaaaaaaaaaa\0\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaaaaaaaa\0\0"| && "aaaaaaaaaaaaaaaaaaaaaaaaaa\0\0"[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaa\0\0"[j] && "aaaaaaaaaaaaaaaaaaaaaaaaaa\0\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaaaaaaaaaaaaaaaaaaaaaaa\0\0"[k] == "aaaaaaaaaaaaaaaaaaaaaaaaaa\0\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaaaaaaaa\0\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaa\0\0"[i] != "aaaaaaaaaaaaaaaaaaaaaaaaaa\0\0"[j];
}
method {:test} Test16() {
var r0, r1 := FindFirstRepeatedChar("\U{0001}a");
expect r0 ==> exists i: int, j: int {:trigger "\U{0001}a"[j], "\U{0001}a"[i]} :: 0 <= i < j < |"\U{0001}a"| && "\U{0001}a"[i] == "\U{0001}a"[j] && "\U{0001}a"[i] == r1 && forall k: int, l: int {:trigger "\U{0001}a"[l], "\U{0001}a"[k]} :: 0 <= k < l < j && "\U{0001}a"[k] == "\U{0001}a"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\U{0001}a"[j], "\U{0001}a"[i]} :: 0 <= i < j < |"\U{0001}a"| ==> "\U{0001}a"[i] != "\U{0001}a"[j];
}
method {:test} Test17() {
var r0, r1 := FindFirstRepeatedChar("\0\U{0004}\U{0002}a\0aaaaaaaa");
expect r0 ==> exists i: int, j: int {:trigger "\0\U{0004}\U{0002}a\0aaaaaaaa"[j], "\0\U{0004}\U{0002}a\0aaaaaaaa"[i]} :: 0 <= i < j < |"\0\U{0004}\U{0002}a\0aaaaaaaa"| && "\0\U{0004}\U{0002}a\0aaaaaaaa"[i] == "\0\U{0004}\U{0002}a\0aaaaaaaa"[j] && "\0\U{0004}\U{0002}a\0aaaaaaaa"[i] == r1 && forall k: int, l: int {:trigger "\0\U{0004}\U{0002}a\0aaaaaaaa"[l], "\0\U{0004}\U{0002}a\0aaaaaaaa"[k]} :: 0 <= k < l < j && "\0\U{0004}\U{0002}a\0aaaaaaaa"[k] == "\0\U{0004}\U{0002}a\0aaaaaaaa"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\0\U{0004}\U{0002}a\0aaaaaaaa"[j], "\0\U{0004}\U{0002}a\0aaaaaaaa"[i]} :: 0 <= i < j < |"\0\U{0004}\U{0002}a\0aaaaaaaa"| ==> "\0\U{0004}\U{0002}a\0aaaaaaaa"[i] != "\0\U{0004}\U{0002}a\0aaaaaaaa"[j];
}
method {:test} Test18() {
var r0, r1 := FindFirstRepeatedChar("a\U{000B}a\ta\U{0007}aaaa\U{0005}aaaaa\U{0003}\U{0001}");
expect r0 ==> exists i: int, j: int {:trigger "a\U{000B}a\ta\U{0007}aaaa\U{0005}aaaaa\U{0003}\U{0001}"[j], "a\U{000B}a\ta\U{0007}aaaa\U{0005}aaaaa\U{0003}\U{0001}"[i]} :: 0 <= i < j < |"a\U{000B}a\ta\U{0007}aaaa\U{0005}aaaaa\U{0003}\U{0001}"| && "a\U{000B}a\ta\U{0007}aaaa\U{0005}aaaaa\U{0003}\U{0001}"[i] == "a\U{000B}a\ta\U{0007}aaaa\U{0005}aaaaa\U{0003}\U{0001}"[j] && "a\U{000B}a\ta\U{0007}aaaa\U{0005}aaaaa\U{0003}\U{0001}"[i] == r1 && forall k: int, l: int {:trigger "a\U{000B}a\ta\U{0007}aaaa\U{0005}aaaaa\U{0003}\U{0001}"[l], "a\U{000B}a\ta\U{0007}aaaa\U{0005}aaaaa\U{0003}\U{0001}"[k]} :: 0 <= k < l < j && "a\U{000B}a\ta\U{0007}aaaa\U{0005}aaaaa\U{0003}\U{0001}"[k] == "a\U{000B}a\ta\U{0007}aaaa\U{0005}aaaaa\U{0003}\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "a\U{000B}a\ta\U{0007}aaaa\U{0005}aaaaa\U{0003}\U{0001}"[j], "a\U{000B}a\ta\U{0007}aaaa\U{0005}aaaaa\U{0003}\U{0001}"[i]} :: 0 <= i < j < |"a\U{000B}a\ta\U{0007}aaaa\U{0005}aaaaa\U{0003}\U{0001}"| ==> "a\U{000B}a\ta\U{0007}aaaa\U{0005}aaaaa\U{0003}\U{0001}"[i] != "a\U{000B}a\ta\U{0007}aaaa\U{0005}aaaaa\U{0003}\U{0001}"[j];
}
method {:test} Test19() {
var r0, r1 := FindFirstRepeatedChar("\0aa\U{0008}a\n\0a\U{0002}\U{0004}aaa\U{0006}aaaaa");
expect r0 ==> exists i: int, j: int {:trigger "\0aa\U{0008}a\n\0a\U{0002}\U{0004}aaa\U{0006}aaaaa"[j], "\0aa\U{0008}a\n\0a\U{0002}\U{0004}aaa\U{0006}aaaaa"[i]} :: 0 <= i < j < |"\0aa\U{0008}a\n\0a\U{0002}\U{0004}aaa\U{0006}aaaaa"| && "\0aa\U{0008}a\n\0a\U{0002}\U{0004}aaa\U{0006}aaaaa"[i] == "\0aa\U{0008}a\n\0a\U{0002}\U{0004}aaa\U{0006}aaaaa"[j] && "\0aa\U{0008}a\n\0a\U{0002}\U{0004}aaa\U{0006}aaaaa"[i] == r1 && forall k: int, l: int {:trigger "\0aa\U{0008}a\n\0a\U{0002}\U{0004}aaa\U{0006}aaaaa"[l], "\0aa\U{0008}a\n\0a\U{0002}\U{0004}aaa\U{0006}aaaaa"[k]} :: 0 <= k < l < j && "\0aa\U{0008}a\n\0a\U{0002}\U{0004}aaa\U{0006}aaaaa"[k] == "\0aa\U{0008}a\n\0a\U{0002}\U{0004}aaa\U{0006}aaaaa"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\0aa\U{0008}a\n\0a\U{0002}\U{0004}aaa\U{0006}aaaaa"[j], "\0aa\U{0008}a\n\0a\U{0002}\U{0004}aaa\U{0006}aaaaa"[i]} :: 0 <= i < j < |"\0aa\U{0008}a\n\0a\U{0002}\U{0004}aaa\U{0006}aaaaa"| ==> "\0aa\U{0008}a\n\0a\U{0002}\U{0004}aaa\U{0006}aaaaa"[i] != "\0aa\U{0008}a\n\0a\U{0002}\U{0004}aaa\U{0006}aaaaa"[j];
}
method {:test} Test20() {
var r0, r1 := FindFirstRepeatedChar("\U{0005}aaaaaaaaaaaaaaaaa\U{000B}\t\U{0007}\U{0003}\U{0001}");
expect r0 ==> exists i: int, j: int {:trigger "\U{0005}aaaaaaaaaaaaaaaaa\U{000B}\t\U{0007}\U{0003}\U{0001}"[j], "\U{0005}aaaaaaaaaaaaaaaaa\U{000B}\t\U{0007}\U{0003}\U{0001}"[i]} :: 0 <= i < j < |"\U{0005}aaaaaaaaaaaaaaaaa\U{000B}\t\U{0007}\U{0003}\U{0001}"| && "\U{0005}aaaaaaaaaaaaaaaaa\U{000B}\t\U{0007}\U{0003}\U{0001}"[i] == "\U{0005}aaaaaaaaaaaaaaaaa\U{000B}\t\U{0007}\U{0003}\U{0001}"[j] && "\U{0005}aaaaaaaaaaaaaaaaa\U{000B}\t\U{0007}\U{0003}\U{0001}"[i] == r1 && forall k: int, l: int {:trigger "\U{0005}aaaaaaaaaaaaaaaaa\U{000B}\t\U{0007}\U{0003}\U{0001}"[l], "\U{0005}aaaaaaaaaaaaaaaaa\U{000B}\t\U{0007}\U{0003}\U{0001}"[k]} :: 0 <= k < l < j && "\U{0005}aaaaaaaaaaaaaaaaa\U{000B}\t\U{0007}\U{0003}\U{0001}"[k] == "\U{0005}aaaaaaaaaaaaaaaaa\U{000B}\t\U{0007}\U{0003}\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\U{0005}aaaaaaaaaaaaaaaaa\U{000B}\t\U{0007}\U{0003}\U{0001}"[j], "\U{0005}aaaaaaaaaaaaaaaaa\U{000B}\t\U{0007}\U{0003}\U{0001}"[i]} :: 0 <= i < j < |"\U{0005}aaaaaaaaaaaaaaaaa\U{000B}\t\U{0007}\U{0003}\U{0001}"| ==> "\U{0005}aaaaaaaaaaaaaaaaa\U{000B}\t\U{0007}\U{0003}\U{0001}"[i] != "\U{0005}aaaaaaaaaaaaaaaaa\U{000B}\t\U{0007}\U{0003}\U{0001}"[j];
}
method {:test} Test21() {
var r0, r1 := FindFirstRepeatedChar("\0a\U{0006}\n\U{0008}a\U{0002}\0aaaaa\U{0004}");
expect r0 ==> exists i: int, j: int {:trigger "\0a\U{0006}\n\U{0008}a\U{0002}\0aaaaa\U{0004}"[j], "\0a\U{0006}\n\U{0008}a\U{0002}\0aaaaa\U{0004}"[i]} :: 0 <= i < j < |"\0a\U{0006}\n\U{0008}a\U{0002}\0aaaaa\U{0004}"| && "\0a\U{0006}\n\U{0008}a\U{0002}\0aaaaa\U{0004}"[i] == "\0a\U{0006}\n\U{0008}a\U{0002}\0aaaaa\U{0004}"[j] && "\0a\U{0006}\n\U{0008}a\U{0002}\0aaaaa\U{0004}"[i] == r1 && forall k: int, l: int {:trigger "\0a\U{0006}\n\U{0008}a\U{0002}\0aaaaa\U{0004}"[l], "\0a\U{0006}\n\U{0008}a\U{0002}\0aaaaa\U{0004}"[k]} :: 0 <= k < l < j && "\0a\U{0006}\n\U{0008}a\U{0002}\0aaaaa\U{0004}"[k] == "\0a\U{0006}\n\U{0008}a\U{0002}\0aaaaa\U{0004}"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\0a\U{0006}\n\U{0008}a\U{0002}\0aaaaa\U{0004}"[j], "\0a\U{0006}\n\U{0008}a\U{0002}\0aaaaa\U{0004}"[i]} :: 0 <= i < j < |"\0a\U{0006}\n\U{0008}a\U{0002}\0aaaaa\U{0004}"| ==> "\0a\U{0006}\n\U{0008}a\U{0002}\0aaaaa\U{0004}"[i] != "\0a\U{0006}\n\U{0008}a\U{0002}\0aaaaa\U{0004}"[j];
}
