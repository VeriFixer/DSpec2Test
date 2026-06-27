// dafny-synthesis_task_id_602.dfy

method {:testEntry} FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i
  ensures !found ==> forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
{
  c := ' ';
  found := false;
  var inner_found := false;
  var i := 0;
  while false
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
var r0, r1 := FindFirstRepeatedChar("aaaaaaaaaaaaaaaaaaaaaaa\0\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaaaaa\0\0"| && "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[i] == "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[j] && "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[k] == "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaaaaa\0\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[i] != "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[j];
}

// REPEAT 1 - TIME: 3.5141799 s

method {:test} Test2() {
var r0, r1 := FindFirstRepeatedChar("\U{0003}\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0003}\U{0001}"| && "\U{0003}\U{0001}"[i] == "\U{0003}\U{0001}"[j] && "\U{0003}\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0003}\U{0001}"[k] == "\U{0003}\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0003}\U{0001}"| ==> "\U{0003}\U{0001}"[i] != "\U{0003}\U{0001}"[j];
}
method {:test} Test3() {
var r0, r1 := FindFirstRepeatedChar("\0\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0\0"| && "\0\0"[i] == "\0\0"[j] && "\0\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0\0"[k] == "\0\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0\0"| ==> "\0\0"[i] != "\0\0"[j];
}

// REPEAT 2 - TIME: 4.899549 s

method {:test} Test4() {
var r0, r1 := FindFirstRepeatedChar("\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0001}"| && "\U{0001}"[i] == "\U{0001}"[j] && "\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0001}"[k] == "\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0001}"| ==> "\U{0001}"[i] != "\U{0001}"[j];
}
method {:test} Test5() {
var r0, r1 := FindFirstRepeatedChar("a\0\U{0002}\0a");
expect r0 ==> exists i, j :: 0 <= i < j < |"a\0\U{0002}\0a"| && "a\0\U{0002}\0a"[i] == "a\0\U{0002}\0a"[j] && "a\0\U{0002}\0a"[i] == r1 && forall k, l :: 0 <= k < l < j && "a\0\U{0002}\0a"[k] == "a\0\U{0002}\0a"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"a\0\U{0002}\0a"| ==> "a\0\U{0002}\0a"[i] != "a\0\U{0002}\0a"[j];
}

// REPEAT 3 - TIME: 6.4078172 s

method {:test} Test6() {
var r0, r1 := FindFirstRepeatedChar("\U{0003}a\U{0007}\U{0001}aaaaaaaaaaaa\U{0005}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0003}a\U{0007}\U{0001}aaaaaaaaaaaa\U{0005}"| && "\U{0003}a\U{0007}\U{0001}aaaaaaaaaaaa\U{0005}"[i] == "\U{0003}a\U{0007}\U{0001}aaaaaaaaaaaa\U{0005}"[j] && "\U{0003}a\U{0007}\U{0001}aaaaaaaaaaaa\U{0005}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0003}a\U{0007}\U{0001}aaaaaaaaaaaa\U{0005}"[k] == "\U{0003}a\U{0007}\U{0001}aaaaaaaaaaaa\U{0005}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0003}a\U{0007}\U{0001}aaaaaaaaaaaa\U{0005}"| ==> "\U{0003}a\U{0007}\U{0001}aaaaaaaaaaaa\U{0005}"[i] != "\U{0003}a\U{0007}\U{0001}aaaaaaaaaaaa\U{0005}"[j];
}
method {:test} Test7() {
var r0, r1 := FindFirstRepeatedChar("\0aaaa\U{0004}aaaaaa\U{0002}aaaaaaa\0aaaa\U{0006}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0aaaa\U{0004}aaaaaa\U{0002}aaaaaaa\0aaaa\U{0006}"| && "\0aaaa\U{0004}aaaaaa\U{0002}aaaaaaa\0aaaa\U{0006}"[i] == "\0aaaa\U{0004}aaaaaa\U{0002}aaaaaaa\0aaaa\U{0006}"[j] && "\0aaaa\U{0004}aaaaaa\U{0002}aaaaaaa\0aaaa\U{0006}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0aaaa\U{0004}aaaaaa\U{0002}aaaaaaa\0aaaa\U{0006}"[k] == "\0aaaa\U{0004}aaaaaa\U{0002}aaaaaaa\0aaaa\U{0006}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0aaaa\U{0004}aaaaaa\U{0002}aaaaaaa\0aaaa\U{0006}"| ==> "\0aaaa\U{0004}aaaaaa\U{0002}aaaaaaa\0aaaa\U{0006}"[i] != "\0aaaa\U{0004}aaaaaa\U{0002}aaaaaaa\0aaaa\U{0006}"[j];
}

// REPEAT 4 - TIME: 8.0473603 s

method {:test} Test8() {
var r0, r1 := FindFirstRepeatedChar("\U{0003}aaaa\taa\U{0005}\U{0001}\U{0007}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0003}aaaa\taa\U{0005}\U{0001}\U{0007}"| && "\U{0003}aaaa\taa\U{0005}\U{0001}\U{0007}"[i] == "\U{0003}aaaa\taa\U{0005}\U{0001}\U{0007}"[j] && "\U{0003}aaaa\taa\U{0005}\U{0001}\U{0007}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0003}aaaa\taa\U{0005}\U{0001}\U{0007}"[k] == "\U{0003}aaaa\taa\U{0005}\U{0001}\U{0007}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0003}aaaa\taa\U{0005}\U{0001}\U{0007}"| ==> "\U{0003}aaaa\taa\U{0005}\U{0001}\U{0007}"[i] != "\U{0003}aaaa\taa\U{0005}\U{0001}\U{0007}"[j];
}
method {:test} Test9() {
var r0, r1 := FindFirstRepeatedChar("\0aaaa\0aaaaa\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0aaaa\0aaaaa\U{0002}"| && "\0aaaa\0aaaaa\U{0002}"[i] == "\0aaaa\0aaaaa\U{0002}"[j] && "\0aaaa\0aaaaa\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0aaaa\0aaaaa\U{0002}"[k] == "\0aaaa\0aaaaa\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0aaaa\0aaaaa\U{0002}"| ==> "\0aaaa\0aaaaa\U{0002}"[i] != "\0aaaa\0aaaaa\U{0002}"[j];
}

// REPEAT 5 - TIME: 9.4697355 s

method {:test} Test10() {
var r0, r1 := FindFirstRepeatedChar("\U{0003}\t\U{0007}\U{000B}aaaaaaaaaaaaaaaaa\U{0005}aa\U{0001}a");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0003}\t\U{0007}\U{000B}aaaaaaaaaaaaaaaaa\U{0005}aa\U{0001}a"| && "\U{0003}\t\U{0007}\U{000B}aaaaaaaaaaaaaaaaa\U{0005}aa\U{0001}a"[i] == "\U{0003}\t\U{0007}\U{000B}aaaaaaaaaaaaaaaaa\U{0005}aa\U{0001}a"[j] && "\U{0003}\t\U{0007}\U{000B}aaaaaaaaaaaaaaaaa\U{0005}aa\U{0001}a"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0003}\t\U{0007}\U{000B}aaaaaaaaaaaaaaaaa\U{0005}aa\U{0001}a"[k] == "\U{0003}\t\U{0007}\U{000B}aaaaaaaaaaaaaaaaa\U{0005}aa\U{0001}a"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0003}\t\U{0007}\U{000B}aaaaaaaaaaaaaaaaa\U{0005}aa\U{0001}a"| ==> "\U{0003}\t\U{0007}\U{000B}aaaaaaaaaaaaaaaaa\U{0005}aa\U{0001}a"[i] != "\U{0003}\t\U{0007}\U{000B}aaaaaaaaaaaaaaaaa\U{0005}aa\U{0001}a"[j];
}
method {:test} Test11() {
var r0, r1 := FindFirstRepeatedChar("\0aaa\U{0006}aaaaaa\U{0004}aaaaa\U{0002}aaaaaaa\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0aaa\U{0006}aaaaaa\U{0004}aaaaa\U{0002}aaaaaaa\0"| && "\0aaa\U{0006}aaaaaa\U{0004}aaaaa\U{0002}aaaaaaa\0"[i] == "\0aaa\U{0006}aaaaaa\U{0004}aaaaa\U{0002}aaaaaaa\0"[j] && "\0aaa\U{0006}aaaaaa\U{0004}aaaaa\U{0002}aaaaaaa\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0aaa\U{0006}aaaaaa\U{0004}aaaaa\U{0002}aaaaaaa\0"[k] == "\0aaa\U{0006}aaaaaa\U{0004}aaaaa\U{0002}aaaaaaa\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0aaa\U{0006}aaaaaa\U{0004}aaaaa\U{0002}aaaaaaa\0"| ==> "\0aaa\U{0006}aaaaaa\U{0004}aaaaa\U{0002}aaaaaaa\0"[i] != "\0aaa\U{0006}aaaaaa\U{0004}aaaaa\U{0002}aaaaaaa\0"[j];
}

// REPEAT 6 - TIME: 10.688754 s

method {:test} Test12() {
var r0, r1 := FindFirstRepeatedChar("\U{0005}\U{0003}\U{0001}\U{0007}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0005}\U{0003}\U{0001}\U{0007}"| && "\U{0005}\U{0003}\U{0001}\U{0007}"[i] == "\U{0005}\U{0003}\U{0001}\U{0007}"[j] && "\U{0005}\U{0003}\U{0001}\U{0007}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0005}\U{0003}\U{0001}\U{0007}"[k] == "\U{0005}\U{0003}\U{0001}\U{0007}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0005}\U{0003}\U{0001}\U{0007}"| ==> "\U{0005}\U{0003}\U{0001}\U{0007}"[i] != "\U{0005}\U{0003}\U{0001}\U{0007}"[j];
}
method {:test} Test13() {
var r0, r1 := FindFirstRepeatedChar("aaaaa\0\U{0006}aa\U{0002}\0\U{0004}");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaa\0\U{0006}aa\U{0002}\0\U{0004}"| && "aaaaa\0\U{0006}aa\U{0002}\0\U{0004}"[i] == "aaaaa\0\U{0006}aa\U{0002}\0\U{0004}"[j] && "aaaaa\0\U{0006}aa\U{0002}\0\U{0004}"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaa\0\U{0006}aa\U{0002}\0\U{0004}"[k] == "aaaaa\0\U{0006}aa\U{0002}\0\U{0004}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaa\0\U{0006}aa\U{0002}\0\U{0004}"| ==> "aaaaa\0\U{0006}aa\U{0002}\0\U{0004}"[i] != "aaaaa\0\U{0006}aa\U{0002}\0\U{0004}"[j];
}

// REPEAT 7 - TIME: 12.0471422 s

method {:test} Test14() {
var r0, r1 := FindFirstRepeatedChar("\U{0003}\U{0007}\U{0005}aaaaaaaa\U{0001}a");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0003}\U{0007}\U{0005}aaaaaaaa\U{0001}a"| && "\U{0003}\U{0007}\U{0005}aaaaaaaa\U{0001}a"[i] == "\U{0003}\U{0007}\U{0005}aaaaaaaa\U{0001}a"[j] && "\U{0003}\U{0007}\U{0005}aaaaaaaa\U{0001}a"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0003}\U{0007}\U{0005}aaaaaaaa\U{0001}a"[k] == "\U{0003}\U{0007}\U{0005}aaaaaaaa\U{0001}a"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0003}\U{0007}\U{0005}aaaaaaaa\U{0001}a"| ==> "\U{0003}\U{0007}\U{0005}aaaaaaaa\U{0001}a"[i] != "\U{0003}\U{0007}\U{0005}aaaaaaaa\U{0001}a"[j];
}
method {:test} Test15() {
var r0, r1 := FindFirstRepeatedChar("\0\U{0004}aaa\0\U{0002}\U{0006}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0\U{0004}aaa\0\U{0002}\U{0006}"| && "\0\U{0004}aaa\0\U{0002}\U{0006}"[i] == "\0\U{0004}aaa\0\U{0002}\U{0006}"[j] && "\0\U{0004}aaa\0\U{0002}\U{0006}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0\U{0004}aaa\0\U{0002}\U{0006}"[k] == "\0\U{0004}aaa\0\U{0002}\U{0006}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0\U{0004}aaa\0\U{0002}\U{0006}"| ==> "\0\U{0004}aaa\0\U{0002}\U{0006}"[i] != "\0\U{0004}aaa\0\U{0002}\U{0006}"[j];
}

// REPEAT 8 - TIME: 13.4016454 s

method {:test} Test16() {
var r0, r1 := FindFirstRepeatedChar("\U{000B}\r\t\U{0007}\U{0005}\U{0003}\U{000F}aa\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{000B}\r\t\U{0007}\U{0005}\U{0003}\U{000F}aa\U{0001}"| && "\U{000B}\r\t\U{0007}\U{0005}\U{0003}\U{000F}aa\U{0001}"[i] == "\U{000B}\r\t\U{0007}\U{0005}\U{0003}\U{000F}aa\U{0001}"[j] && "\U{000B}\r\t\U{0007}\U{0005}\U{0003}\U{000F}aa\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{000B}\r\t\U{0007}\U{0005}\U{0003}\U{000F}aa\U{0001}"[k] == "\U{000B}\r\t\U{0007}\U{0005}\U{0003}\U{000F}aa\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{000B}\r\t\U{0007}\U{0005}\U{0003}\U{000F}aa\U{0001}"| ==> "\U{000B}\r\t\U{0007}\U{0005}\U{0003}\U{000F}aa\U{0001}"[i] != "\U{000B}\r\t\U{0007}\U{0005}\U{0003}\U{000F}aa\U{0001}"[j];
}
method {:test} Test17() {
var r0, r1 := FindFirstRepeatedChar("\0\0\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0\0\U{0002}"| && "\0\0\U{0002}"[i] == "\0\0\U{0002}"[j] && "\0\0\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0\0\U{0002}"[k] == "\0\0\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0\0\U{0002}"| ==> "\0\0\U{0002}"[i] != "\0\0\U{0002}"[j];
}

// REPEAT 9 - TIME: 14.7403184 s

method {:test} Test18() {
var r0, r1 := FindFirstRepeatedChar("\U{000B}aaaa\t\U{0001}a\U{0007}\U{0005}\U{0003}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{000B}aaaa\t\U{0001}a\U{0007}\U{0005}\U{0003}"| && "\U{000B}aaaa\t\U{0001}a\U{0007}\U{0005}\U{0003}"[i] == "\U{000B}aaaa\t\U{0001}a\U{0007}\U{0005}\U{0003}"[j] && "\U{000B}aaaa\t\U{0001}a\U{0007}\U{0005}\U{0003}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{000B}aaaa\t\U{0001}a\U{0007}\U{0005}\U{0003}"[k] == "\U{000B}aaaa\t\U{0001}a\U{0007}\U{0005}\U{0003}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{000B}aaaa\t\U{0001}a\U{0007}\U{0005}\U{0003}"| ==> "\U{000B}aaaa\t\U{0001}a\U{0007}\U{0005}\U{0003}"[i] != "\U{000B}aaaa\t\U{0001}a\U{0007}\U{0005}\U{0003}"[j];
}
method {:test} Test19() {
var r0, r1 := FindFirstRepeatedChar("\0aaa\U{0002}\0\U{0004}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0aaa\U{0002}\0\U{0004}"| && "\0aaa\U{0002}\0\U{0004}"[i] == "\0aaa\U{0002}\0\U{0004}"[j] && "\0aaa\U{0002}\0\U{0004}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0aaa\U{0002}\0\U{0004}"[k] == "\0aaa\U{0002}\0\U{0004}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0aaa\U{0002}\0\U{0004}"| ==> "\0aaa\U{0002}\0\U{0004}"[i] != "\0aaa\U{0002}\0\U{0004}"[j];
}

// REPEAT 10 - TIME: 15.9118594 s
