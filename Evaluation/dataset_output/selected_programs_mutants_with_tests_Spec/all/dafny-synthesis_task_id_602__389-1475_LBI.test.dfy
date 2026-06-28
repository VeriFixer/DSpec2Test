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
var r0, r1 := FindFirstRepeatedChar("aaaaaaaaaaaaaaaaaaaaaaa\0\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaaaaa\0\0"| && "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[i] == "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[j] && "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[k] == "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaaaaa\0\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[i] != "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[j];
}

// REPEAT 1 - TIME: 3.5767112 s

method {:test} Test2() {
var r0, r1 := FindFirstRepeatedChar("\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0001}"| && "\U{0001}"[i] == "\U{0001}"[j] && "\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0001}"[k] == "\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0001}"| ==> "\U{0001}"[i] != "\U{0001}"[j];
}
method {:test} Test3() {
var r0, r1 := FindFirstRepeatedChar("\0\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0\0"| && "\0\0"[i] == "\0\0"[j] && "\0\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0\0"[k] == "\0\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0\0"| ==> "\0\0"[i] != "\0\0"[j];
}

// REPEAT 2 - TIME: 5.1899612 s

method {:test} Test4() {
var r0, r1 := FindFirstRepeatedChar("aaaaaaaaaaaaaaaaaaaa\U{0003}\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaa\U{0003}\U{0001}"| && "aaaaaaaaaaaaaaaaaaaa\U{0003}\U{0001}"[i] == "aaaaaaaaaaaaaaaaaaaa\U{0003}\U{0001}"[j] && "aaaaaaaaaaaaaaaaaaaa\U{0003}\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaaaaaaaaaaaaaaaaa\U{0003}\U{0001}"[k] == "aaaaaaaaaaaaaaaaaaaa\U{0003}\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaa\U{0003}\U{0001}"| ==> "aaaaaaaaaaaaaaaaaaaa\U{0003}\U{0001}"[i] != "aaaaaaaaaaaaaaaaaaaa\U{0003}\U{0001}"[j];
}
method {:test} Test5() {
var r0, r1 := FindFirstRepeatedChar("a\0\0aaaaaaaaaa\U{0002}aaaaaaaaaaa\U{0004}");
expect r0 ==> exists i, j :: 0 <= i < j < |"a\0\0aaaaaaaaaa\U{0002}aaaaaaaaaaa\U{0004}"| && "a\0\0aaaaaaaaaa\U{0002}aaaaaaaaaaa\U{0004}"[i] == "a\0\0aaaaaaaaaa\U{0002}aaaaaaaaaaa\U{0004}"[j] && "a\0\0aaaaaaaaaa\U{0002}aaaaaaaaaaa\U{0004}"[i] == r1 && forall k, l :: 0 <= k < l < j && "a\0\0aaaaaaaaaa\U{0002}aaaaaaaaaaa\U{0004}"[k] == "a\0\0aaaaaaaaaa\U{0002}aaaaaaaaaaa\U{0004}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"a\0\0aaaaaaaaaa\U{0002}aaaaaaaaaaa\U{0004}"| ==> "a\0\0aaaaaaaaaa\U{0002}aaaaaaaaaaa\U{0004}"[i] != "a\0\0aaaaaaaaaa\U{0002}aaaaaaaaaaa\U{0004}"[j];
}

// REPEAT 3 - TIME: 6.8097386 s

method {:test} Test6() {
var r0, r1 := FindFirstRepeatedChar("aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\U{0005}\U{0003}\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\U{0005}\U{0003}\U{0001}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\U{0005}\U{0003}\U{0001}"[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\U{0005}\U{0003}\U{0001}"[j] && "aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\U{0005}\U{0003}\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\U{0005}\U{0003}\U{0001}"[k] == "aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\U{0005}\U{0003}\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\U{0005}\U{0003}\U{0001}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\U{0005}\U{0003}\U{0001}"[i] != "aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\U{0005}\U{0003}\U{0001}"[j];
}
method {:test} Test7() {
var r0, r1 := FindFirstRepeatedChar("\0\U{0004}aaaaaaa\0aaaaaaaaaaaa\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0\U{0004}aaaaaaa\0aaaaaaaaaaaa\U{0002}"| && "\0\U{0004}aaaaaaa\0aaaaaaaaaaaa\U{0002}"[i] == "\0\U{0004}aaaaaaa\0aaaaaaaaaaaa\U{0002}"[j] && "\0\U{0004}aaaaaaa\0aaaaaaaaaaaa\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0\U{0004}aaaaaaa\0aaaaaaaaaaaa\U{0002}"[k] == "\0\U{0004}aaaaaaa\0aaaaaaaaaaaa\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0\U{0004}aaaaaaa\0aaaaaaaaaaaa\U{0002}"| ==> "\0\U{0004}aaaaaaa\0aaaaaaaaaaaa\U{0002}"[i] != "\0\U{0004}aaaaaaa\0aaaaaaaaaaaa\U{0002}"[j];
}

// REPEAT 4 - TIME: 8.5078454 s

method {:test} Test8() {
var r0, r1 := FindFirstRepeatedChar("\U{0005}aaaaaaaaaaaaaaaaaaaaa\U{0007}aa\U{000B}\r\t\U{0003}\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0005}aaaaaaaaaaaaaaaaaaaaa\U{0007}aa\U{000B}\r\t\U{0003}\U{0001}"| && "\U{0005}aaaaaaaaaaaaaaaaaaaaa\U{0007}aa\U{000B}\r\t\U{0003}\U{0001}"[i] == "\U{0005}aaaaaaaaaaaaaaaaaaaaa\U{0007}aa\U{000B}\r\t\U{0003}\U{0001}"[j] && "\U{0005}aaaaaaaaaaaaaaaaaaaaa\U{0007}aa\U{000B}\r\t\U{0003}\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0005}aaaaaaaaaaaaaaaaaaaaa\U{0007}aa\U{000B}\r\t\U{0003}\U{0001}"[k] == "\U{0005}aaaaaaaaaaaaaaaaaaaaa\U{0007}aa\U{000B}\r\t\U{0003}\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0005}aaaaaaaaaaaaaaaaaaaaa\U{0007}aa\U{000B}\r\t\U{0003}\U{0001}"| ==> "\U{0005}aaaaaaaaaaaaaaaaaaaaa\U{0007}aa\U{000B}\r\t\U{0003}\U{0001}"[i] != "\U{0005}aaaaaaaaaaaaaaaaaaaaa\U{0007}aa\U{000B}\r\t\U{0003}\U{0001}"[j];
}
method {:test} Test9() {
var r0, r1 := FindFirstRepeatedChar("a\0\0aaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0006}\U{0004}");
expect r0 ==> exists i, j :: 0 <= i < j < |"a\0\0aaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0006}\U{0004}"| && "a\0\0aaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0006}\U{0004}"[i] == "a\0\0aaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0006}\U{0004}"[j] && "a\0\0aaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0006}\U{0004}"[i] == r1 && forall k, l :: 0 <= k < l < j && "a\0\0aaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0006}\U{0004}"[k] == "a\0\0aaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0006}\U{0004}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"a\0\0aaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0006}\U{0004}"| ==> "a\0\0aaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0006}\U{0004}"[i] != "a\0\0aaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0006}\U{0004}"[j];
}

// REPEAT 5 - TIME: 10.1193077 s

method {:test} Test10() {
var r0, r1 := FindFirstRepeatedChar("\U{0003}\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0003}\U{0001}"| && "\U{0003}\U{0001}"[i] == "\U{0003}\U{0001}"[j] && "\U{0003}\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0003}\U{0001}"[k] == "\U{0003}\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0003}\U{0001}"| ==> "\U{0003}\U{0001}"[i] != "\U{0003}\U{0001}"[j];
}
method {:test} Test11() {
var r0, r1 := FindFirstRepeatedChar("a\0\0aaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}a\U{0008}a\U{0002}\n");
expect r0 ==> exists i, j :: 0 <= i < j < |"a\0\0aaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}a\U{0008}a\U{0002}\n"| && "a\0\0aaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}a\U{0008}a\U{0002}\n"[i] == "a\0\0aaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}a\U{0008}a\U{0002}\n"[j] && "a\0\0aaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}a\U{0008}a\U{0002}\n"[i] == r1 && forall k, l :: 0 <= k < l < j && "a\0\0aaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}a\U{0008}a\U{0002}\n"[k] == "a\0\0aaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}a\U{0008}a\U{0002}\n"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"a\0\0aaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}a\U{0008}a\U{0002}\n"| ==> "a\0\0aaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}a\U{0008}a\U{0002}\n"[i] != "a\0\0aaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}a\U{0008}a\U{0002}\n"[j];
}

// REPEAT 6 - TIME: 11.3578898 s

method {:test} Test12() {
var r0, r1 := FindFirstRepeatedChar("\U{0001}\U{000F}\t\U{0003}\U{0005}\U{000B}\raaaaaaaaaaaaaaa\U{0007}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0001}\U{000F}\t\U{0003}\U{0005}\U{000B}\raaaaaaaaaaaaaaa\U{0007}"| && "\U{0001}\U{000F}\t\U{0003}\U{0005}\U{000B}\raaaaaaaaaaaaaaa\U{0007}"[i] == "\U{0001}\U{000F}\t\U{0003}\U{0005}\U{000B}\raaaaaaaaaaaaaaa\U{0007}"[j] && "\U{0001}\U{000F}\t\U{0003}\U{0005}\U{000B}\raaaaaaaaaaaaaaa\U{0007}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0001}\U{000F}\t\U{0003}\U{0005}\U{000B}\raaaaaaaaaaaaaaa\U{0007}"[k] == "\U{0001}\U{000F}\t\U{0003}\U{0005}\U{000B}\raaaaaaaaaaaaaaa\U{0007}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0001}\U{000F}\t\U{0003}\U{0005}\U{000B}\raaaaaaaaaaaaaaa\U{0007}"| ==> "\U{0001}\U{000F}\t\U{0003}\U{0005}\U{000B}\raaaaaaaaaaaaaaa\U{0007}"[i] != "\U{0001}\U{000F}\t\U{0003}\U{0005}\U{000B}\raaaaaaaaaaaaaaa\U{0007}"[j];
}
method {:test} Test13() {
var r0, r1 := FindFirstRepeatedChar("\0aaaaaaaaaaaaaaaaaaa\U{0004}\0\U{0002}\U{0008}aaaa\U{0006}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0aaaaaaaaaaaaaaaaaaa\U{0004}\0\U{0002}\U{0008}aaaa\U{0006}"| && "\0aaaaaaaaaaaaaaaaaaa\U{0004}\0\U{0002}\U{0008}aaaa\U{0006}"[i] == "\0aaaaaaaaaaaaaaaaaaa\U{0004}\0\U{0002}\U{0008}aaaa\U{0006}"[j] && "\0aaaaaaaaaaaaaaaaaaa\U{0004}\0\U{0002}\U{0008}aaaa\U{0006}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0aaaaaaaaaaaaaaaaaaa\U{0004}\0\U{0002}\U{0008}aaaa\U{0006}"[k] == "\0aaaaaaaaaaaaaaaaaaa\U{0004}\0\U{0002}\U{0008}aaaa\U{0006}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0aaaaaaaaaaaaaaaaaaa\U{0004}\0\U{0002}\U{0008}aaaa\U{0006}"| ==> "\0aaaaaaaaaaaaaaaaaaa\U{0004}\0\U{0002}\U{0008}aaaa\U{0006}"[i] != "\0aaaaaaaaaaaaaaaaaaa\U{0004}\0\U{0002}\U{0008}aaaa\U{0006}"[j];
}

// REPEAT 7 - TIME: 12.5551294 s

method {:test} Test14() {
var r0, r1 := FindFirstRepeatedChar("\U{000B}\r\U{000F}aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}\U{0007}\t\U{0005}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{000B}\r\U{000F}aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}\U{0007}\t\U{0005}"| && "\U{000B}\r\U{000F}aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}\U{0007}\t\U{0005}"[i] == "\U{000B}\r\U{000F}aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}\U{0007}\t\U{0005}"[j] && "\U{000B}\r\U{000F}aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}\U{0007}\t\U{0005}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{000B}\r\U{000F}aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}\U{0007}\t\U{0005}"[k] == "\U{000B}\r\U{000F}aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}\U{0007}\t\U{0005}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{000B}\r\U{000F}aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}\U{0007}\t\U{0005}"| ==> "\U{000B}\r\U{000F}aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}\U{0007}\t\U{0005}"[i] != "\U{000B}\r\U{000F}aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}\U{0007}\t\U{0005}"[j];
}
method {:test} Test15() {
var r0, r1 := FindFirstRepeatedChar("\0\U{0005}a\U{0003}\0\U{0007}aaaaaaaaaaaaaaaa\U{0001}aaa\ta");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0\U{0005}a\U{0003}\0\U{0007}aaaaaaaaaaaaaaaa\U{0001}aaa\ta"| && "\0\U{0005}a\U{0003}\0\U{0007}aaaaaaaaaaaaaaaa\U{0001}aaa\ta"[i] == "\0\U{0005}a\U{0003}\0\U{0007}aaaaaaaaaaaaaaaa\U{0001}aaa\ta"[j] && "\0\U{0005}a\U{0003}\0\U{0007}aaaaaaaaaaaaaaaa\U{0001}aaa\ta"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0\U{0005}a\U{0003}\0\U{0007}aaaaaaaaaaaaaaaa\U{0001}aaa\ta"[k] == "\0\U{0005}a\U{0003}\0\U{0007}aaaaaaaaaaaaaaaa\U{0001}aaa\ta"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0\U{0005}a\U{0003}\0\U{0007}aaaaaaaaaaaaaaaa\U{0001}aaa\ta"| ==> "\0\U{0005}a\U{0003}\0\U{0007}aaaaaaaaaaaaaaaa\U{0001}aaa\ta"[i] != "\0\U{0005}a\U{0003}\0\U{0007}aaaaaaaaaaaaaaaa\U{0001}aaa\ta"[j];
}

// REPEAT 8 - TIME: 13.976852 s

method {:test} Test16() {
var r0, r1 := FindFirstRepeatedChar("\t\U{0007}aaaaaaaaaaaaaaaaaa\U{0001}\U{0003}\U{0005}aaaa");
expect r0 ==> exists i, j :: 0 <= i < j < |"\t\U{0007}aaaaaaaaaaaaaaaaaa\U{0001}\U{0003}\U{0005}aaaa"| && "\t\U{0007}aaaaaaaaaaaaaaaaaa\U{0001}\U{0003}\U{0005}aaaa"[i] == "\t\U{0007}aaaaaaaaaaaaaaaaaa\U{0001}\U{0003}\U{0005}aaaa"[j] && "\t\U{0007}aaaaaaaaaaaaaaaaaa\U{0001}\U{0003}\U{0005}aaaa"[i] == r1 && forall k, l :: 0 <= k < l < j && "\t\U{0007}aaaaaaaaaaaaaaaaaa\U{0001}\U{0003}\U{0005}aaaa"[k] == "\t\U{0007}aaaaaaaaaaaaaaaaaa\U{0001}\U{0003}\U{0005}aaaa"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\t\U{0007}aaaaaaaaaaaaaaaaaa\U{0001}\U{0003}\U{0005}aaaa"| ==> "\t\U{0007}aaaaaaaaaaaaaaaaaa\U{0001}\U{0003}\U{0005}aaaa"[i] != "\t\U{0007}aaaaaaaaaaaaaaaaaa\U{0001}\U{0003}\U{0005}aaaa"[j];
}
method {:test} Test17() {
var r0, r1 := FindFirstRepeatedChar("aa\0aaaaaaaaaaaaaaaaaaaaaaa\U{0006}\0\U{0002}\U{0004}");
expect r0 ==> exists i, j :: 0 <= i < j < |"aa\0aaaaaaaaaaaaaaaaaaaaaaa\U{0006}\0\U{0002}\U{0004}"| && "aa\0aaaaaaaaaaaaaaaaaaaaaaa\U{0006}\0\U{0002}\U{0004}"[i] == "aa\0aaaaaaaaaaaaaaaaaaaaaaa\U{0006}\0\U{0002}\U{0004}"[j] && "aa\0aaaaaaaaaaaaaaaaaaaaaaa\U{0006}\0\U{0002}\U{0004}"[i] == r1 && forall k, l :: 0 <= k < l < j && "aa\0aaaaaaaaaaaaaaaaaaaaaaa\U{0006}\0\U{0002}\U{0004}"[k] == "aa\0aaaaaaaaaaaaaaaaaaaaaaa\U{0006}\0\U{0002}\U{0004}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aa\0aaaaaaaaaaaaaaaaaaaaaaa\U{0006}\0\U{0002}\U{0004}"| ==> "aa\0aaaaaaaaaaaaaaaaaaaaaaa\U{0006}\0\U{0002}\U{0004}"[i] != "aa\0aaaaaaaaaaaaaaaaaaaaaaa\U{0006}\0\U{0002}\U{0004}"[j];
}

// REPEAT 9 - TIME: 15.1943319 s

method {:test} Test18() {
var r0, r1 := FindFirstRepeatedChar("\U{0003}\t\U{0007}\U{000B}\raaaaaaaaaaaaaaaaa\U{0005}aaa\U{000F}\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0003}\t\U{0007}\U{000B}\raaaaaaaaaaaaaaaaa\U{0005}aaa\U{000F}\U{0001}"| && "\U{0003}\t\U{0007}\U{000B}\raaaaaaaaaaaaaaaaa\U{0005}aaa\U{000F}\U{0001}"[i] == "\U{0003}\t\U{0007}\U{000B}\raaaaaaaaaaaaaaaaa\U{0005}aaa\U{000F}\U{0001}"[j] && "\U{0003}\t\U{0007}\U{000B}\raaaaaaaaaaaaaaaaa\U{0005}aaa\U{000F}\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0003}\t\U{0007}\U{000B}\raaaaaaaaaaaaaaaaa\U{0005}aaa\U{000F}\U{0001}"[k] == "\U{0003}\t\U{0007}\U{000B}\raaaaaaaaaaaaaaaaa\U{0005}aaa\U{000F}\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0003}\t\U{0007}\U{000B}\raaaaaaaaaaaaaaaaa\U{0005}aaa\U{000F}\U{0001}"| ==> "\U{0003}\t\U{0007}\U{000B}\raaaaaaaaaaaaaaaaa\U{0005}aaa\U{000F}\U{0001}"[i] != "\U{0003}\t\U{0007}\U{000B}\raaaaaaaaaaaaaaaaa\U{0005}aaa\U{000F}\U{0001}"[j];
}
method {:test} Test19() {
var r0, r1 := FindFirstRepeatedChar("\0\0\U{000C}\taaaaaaaaaaaaaaaaaa\U{0001}\U{0003}a\U{0005}\U{000E}\U{0007}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0\0\U{000C}\taaaaaaaaaaaaaaaaaa\U{0001}\U{0003}a\U{0005}\U{000E}\U{0007}"| && "\0\0\U{000C}\taaaaaaaaaaaaaaaaaa\U{0001}\U{0003}a\U{0005}\U{000E}\U{0007}"[i] == "\0\0\U{000C}\taaaaaaaaaaaaaaaaaa\U{0001}\U{0003}a\U{0005}\U{000E}\U{0007}"[j] && "\0\0\U{000C}\taaaaaaaaaaaaaaaaaa\U{0001}\U{0003}a\U{0005}\U{000E}\U{0007}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0\0\U{000C}\taaaaaaaaaaaaaaaaaa\U{0001}\U{0003}a\U{0005}\U{000E}\U{0007}"[k] == "\0\0\U{000C}\taaaaaaaaaaaaaaaaaa\U{0001}\U{0003}a\U{0005}\U{000E}\U{0007}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0\0\U{000C}\taaaaaaaaaaaaaaaaaa\U{0001}\U{0003}a\U{0005}\U{000E}\U{0007}"| ==> "\0\0\U{000C}\taaaaaaaaaaaaaaaaaa\U{0001}\U{0003}a\U{0005}\U{000E}\U{0007}"[i] != "\0\0\U{000C}\taaaaaaaaaaaaaaaaaa\U{0001}\U{0003}a\U{0005}\U{000E}\U{0007}"[j];
}

// REPEAT 10 - TIME: 17.1187582 s
