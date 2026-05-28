// dafny-synthesis_task_id_602.dfy

method {:testEntry} FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i
  ensures !found ==> forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
{
  c := ' ';
  found := false;
  var inner_found := false;
  var i := 0;
  while i < |s| && !found
    invariant 0 <= i <= |s|
    invariant found == inner_found
    invariant found ==> exists ii, jj :: 0 <= ii < i && ii < jj < |s| && s[ii] == s[jj] && s[ii] == c && forall k, l :: 0 <= k < l < jj && s[k] == s[l] ==> k >= ii
    invariant !found <==> forall ii, jj :: 0 <= ii < i && ii < jj < |s| ==> s[ii] != s[jj]
  {
    break;
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
var r0, r1 := FindFirstRepeatedChar("aaaaaaaaaaaaaaaaaaaaaa\0\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaaaa\0\0"| && "aaaaaaaaaaaaaaaaaaaaaa\0\0"[i] == "aaaaaaaaaaaaaaaaaaaaaa\0\0"[j] && "aaaaaaaaaaaaaaaaaaaaaa\0\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaaaaaaaaaaaaaaaaaaa\0\0"[k] == "aaaaaaaaaaaaaaaaaaaaaa\0\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaaaa\0\0"| ==> "aaaaaaaaaaaaaaaaaaaaaa\0\0"[i] != "aaaaaaaaaaaaaaaaaaaaaa\0\0"[j];
}
method {:test} Test2() {
var r0, r1 := FindFirstRepeatedChar("\U{0003}\U{0001}");
expect r0 ==> exists i: int, j: int {:trigger "\U{0003}\U{0001}"[j], "\U{0003}\U{0001}"[i]} :: 0 <= i < j < |"\U{0003}\U{0001}"| && "\U{0003}\U{0001}"[i] == "\U{0003}\U{0001}"[j] && "\U{0003}\U{0001}"[i] == r1 && forall k: int, l: int {:trigger "\U{0003}\U{0001}"[l], "\U{0003}\U{0001}"[k]} :: 0 <= k < l < j && "\U{0003}\U{0001}"[k] == "\U{0003}\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\U{0003}\U{0001}"[j], "\U{0003}\U{0001}"[i]} :: 0 <= i < j < |"\U{0003}\U{0001}"| ==> "\U{0003}\U{0001}"[i] != "\U{0003}\U{0001}"[j];
}
method {:test} Test3() {
var r0, r1 := FindFirstRepeatedChar("aa\0\0");
expect r0 ==> exists i: int, j: int {:trigger "aa\0\0"[j], "aa\0\0"[i]} :: 0 <= i < j < |"aa\0\0"| && "aa\0\0"[i] == "aa\0\0"[j] && "aa\0\0"[i] == r1 && forall k: int, l: int {:trigger "aa\0\0"[l], "aa\0\0"[k]} :: 0 <= k < l < j && "aa\0\0"[k] == "aa\0\0"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "aa\0\0"[j], "aa\0\0"[i]} :: 0 <= i < j < |"aa\0\0"| ==> "aa\0\0"[i] != "aa\0\0"[j];
}
method {:test} Test4() {
var r0, r1 := FindFirstRepeatedChar("\U{0001}");
expect r0 ==> exists i: int, j: int {:trigger "\U{0001}"[j], "\U{0001}"[i]} :: 0 <= i < j < |"\U{0001}"| && "\U{0001}"[i] == "\U{0001}"[j] && "\U{0001}"[i] == r1 && forall k: int, l: int {:trigger "\U{0001}"[l], "\U{0001}"[k]} :: 0 <= k < l < j && "\U{0001}"[k] == "\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\U{0001}"[j], "\U{0001}"[i]} :: 0 <= i < j < |"\U{0001}"| ==> "\U{0001}"[i] != "\U{0001}"[j];
}
method {:test} Test5() {
var r0, r1 := FindFirstRepeatedChar("\0a\0");
expect r0 ==> exists i: int, j: int {:trigger "\0a\0"[j], "\0a\0"[i]} :: 0 <= i < j < |"\0a\0"| && "\0a\0"[i] == "\0a\0"[j] && "\0a\0"[i] == r1 && forall k: int, l: int {:trigger "\0a\0"[l], "\0a\0"[k]} :: 0 <= k < l < j && "\0a\0"[k] == "\0a\0"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\0a\0"[j], "\0a\0"[i]} :: 0 <= i < j < |"\0a\0"| ==> "\0a\0"[i] != "\0a\0"[j];
}
method {:test} Test6() {
var r0, r1 := FindFirstRepeatedChar("\U{0001}a");
expect r0 ==> exists i: int, j: int {:trigger "\U{0001}a"[j], "\U{0001}a"[i]} :: 0 <= i < j < |"\U{0001}a"| && "\U{0001}a"[i] == "\U{0001}a"[j] && "\U{0001}a"[i] == r1 && forall k: int, l: int {:trigger "\U{0001}a"[l], "\U{0001}a"[k]} :: 0 <= k < l < j && "\U{0001}a"[k] == "\U{0001}a"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\U{0001}a"[j], "\U{0001}a"[i]} :: 0 <= i < j < |"\U{0001}a"| ==> "\U{0001}a"[i] != "\U{0001}a"[j];
}
method {:test} Test7() {
var r0, r1 := FindFirstRepeatedChar("\0a\0");
expect r0 ==> exists i: int, j: int {:trigger "\0a\0"[j], "\0a\0"[i]} :: 0 <= i < j < |"\0a\0"| && "\0a\0"[i] == "\0a\0"[j] && "\0a\0"[i] == r1 && forall k: int, l: int {:trigger "\0a\0"[l], "\0a\0"[k]} :: 0 <= k < l < j && "\0a\0"[k] == "\0a\0"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\0a\0"[j], "\0a\0"[i]} :: 0 <= i < j < |"\0a\0"| ==> "\0a\0"[i] != "\0a\0"[j];
}
method {:test} Test8() {
var r0, r1 := FindFirstRepeatedChar("\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaa\t\U{0007}\U{0001}");
expect r0 ==> exists i: int, j: int {:trigger "\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaa\t\U{0007}\U{0001}"[j], "\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaa\t\U{0007}\U{0001}"[i]} :: 0 <= i < j < |"\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaa\t\U{0007}\U{0001}"| && "\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaa\t\U{0007}\U{0001}"[i] == "\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaa\t\U{0007}\U{0001}"[j] && "\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaa\t\U{0007}\U{0001}"[i] == r1 && forall k: int, l: int {:trigger "\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaa\t\U{0007}\U{0001}"[l], "\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaa\t\U{0007}\U{0001}"[k]} :: 0 <= k < l < j && "\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaa\t\U{0007}\U{0001}"[k] == "\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaa\t\U{0007}\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaa\t\U{0007}\U{0001}"[j], "\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaa\t\U{0007}\U{0001}"[i]} :: 0 <= i < j < |"\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaa\t\U{0007}\U{0001}"| ==> "\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaa\t\U{0007}\U{0001}"[i] != "\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaa\t\U{0007}\U{0001}"[j];
}
method {:test} Test9() {
var r0, r1 := FindFirstRepeatedChar("\0a\0");
expect r0 ==> exists i: int, j: int {:trigger "\0a\0"[j], "\0a\0"[i]} :: 0 <= i < j < |"\0a\0"| && "\0a\0"[i] == "\0a\0"[j] && "\0a\0"[i] == r1 && forall k: int, l: int {:trigger "\0a\0"[l], "\0a\0"[k]} :: 0 <= k < l < j && "\0a\0"[k] == "\0a\0"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\0a\0"[j], "\0a\0"[i]} :: 0 <= i < j < |"\0a\0"| ==> "\0a\0"[i] != "\0a\0"[j];
}
method {:test} Test10() {
var r0, r1 := FindFirstRepeatedChar("\t\U{0005}aa\U{0007}aaaaaaaaa\U{0003}\U{0001}aaaaaaaaa");
expect r0 ==> exists i: int, j: int {:trigger "\t\U{0005}aa\U{0007}aaaaaaaaa\U{0003}\U{0001}aaaaaaaaa"[j], "\t\U{0005}aa\U{0007}aaaaaaaaa\U{0003}\U{0001}aaaaaaaaa"[i]} :: 0 <= i < j < |"\t\U{0005}aa\U{0007}aaaaaaaaa\U{0003}\U{0001}aaaaaaaaa"| && "\t\U{0005}aa\U{0007}aaaaaaaaa\U{0003}\U{0001}aaaaaaaaa"[i] == "\t\U{0005}aa\U{0007}aaaaaaaaa\U{0003}\U{0001}aaaaaaaaa"[j] && "\t\U{0005}aa\U{0007}aaaaaaaaa\U{0003}\U{0001}aaaaaaaaa"[i] == r1 && forall k: int, l: int {:trigger "\t\U{0005}aa\U{0007}aaaaaaaaa\U{0003}\U{0001}aaaaaaaaa"[l], "\t\U{0005}aa\U{0007}aaaaaaaaa\U{0003}\U{0001}aaaaaaaaa"[k]} :: 0 <= k < l < j && "\t\U{0005}aa\U{0007}aaaaaaaaa\U{0003}\U{0001}aaaaaaaaa"[k] == "\t\U{0005}aa\U{0007}aaaaaaaaa\U{0003}\U{0001}aaaaaaaaa"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\t\U{0005}aa\U{0007}aaaaaaaaa\U{0003}\U{0001}aaaaaaaaa"[j], "\t\U{0005}aa\U{0007}aaaaaaaaa\U{0003}\U{0001}aaaaaaaaa"[i]} :: 0 <= i < j < |"\t\U{0005}aa\U{0007}aaaaaaaaa\U{0003}\U{0001}aaaaaaaaa"| ==> "\t\U{0005}aa\U{0007}aaaaaaaaa\U{0003}\U{0001}aaaaaaaaa"[i] != "\t\U{0005}aa\U{0007}aaaaaaaaa\U{0003}\U{0001}aaaaaaaaa"[j];
}
method {:test} Test11() {
var r0, r1 := FindFirstRepeatedChar("\0\U{0002}\0");
expect r0 ==> exists i: int, j: int {:trigger "\0\U{0002}\0"[j], "\0\U{0002}\0"[i]} :: 0 <= i < j < |"\0\U{0002}\0"| && "\0\U{0002}\0"[i] == "\0\U{0002}\0"[j] && "\0\U{0002}\0"[i] == r1 && forall k: int, l: int {:trigger "\0\U{0002}\0"[l], "\0\U{0002}\0"[k]} :: 0 <= k < l < j && "\0\U{0002}\0"[k] == "\0\U{0002}\0"[l] ==> k >= i;
expect !r0 ==> forall i: int, j: int {:trigger "\0\U{0002}\0"[j], "\0\U{0002}\0"[i]} :: 0 <= i < j < |"\0\U{0002}\0"| ==> "\0\U{0002}\0"[i] != "\0\U{0002}\0"[j];
}
