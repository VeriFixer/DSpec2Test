// dafny-synthesis_task_id_602.dfy

method {:testEntry} FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i
  ensures !found ==> forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
{
  c := ' ';
  found := false;
  var inner_found := false;
  var i := 0;
  while i < |s| <==> !found
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
var r0, r1 := FindFirstRepeatedChar("aaaaaaaaaaaaaaaaaaaaaaa\0\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaaaaa\0\0"| && "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[i] == "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[j] && "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[k] == "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaaaaa\0\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[i] != "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[j];
}
method {:test} Test10() {
var r0, r1 := FindFirstRepeatedChar("aaaaa\0\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaa\0\0"| && "aaaaa\0\0"[i] == "aaaaa\0\0"[j] && "aaaaa\0\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaa\0\0"[k] == "aaaaa\0\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaa\0\0"| ==> "aaaaa\0\0"[i] != "aaaaa\0\0"[j];
}

// REPEAT 1 - TIME: 14.7928272 s

method {:test} Test16() {
var r0, r1 := FindFirstRepeatedChar("\U{0007}a\U{0005}\U{0003}\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0007}a\U{0005}\U{0003}\U{0001}"| && "\U{0007}a\U{0005}\U{0003}\U{0001}"[i] == "\U{0007}a\U{0005}\U{0003}\U{0001}"[j] && "\U{0007}a\U{0005}\U{0003}\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0007}a\U{0005}\U{0003}\U{0001}"[k] == "\U{0007}a\U{0005}\U{0003}\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0007}a\U{0005}\U{0003}\U{0001}"| ==> "\U{0007}a\U{0005}\U{0003}\U{0001}"[i] != "\U{0007}a\U{0005}\U{0003}\U{0001}"[j];
}
method {:test} Test17() {
var r0, r1 := FindFirstRepeatedChar("\0\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0\0"| && "\0\0"[i] == "\0\0"[j] && "\0\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0\0"[k] == "\0\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0\0"| ==> "\0\0"[i] != "\0\0"[j];
}

// REPEAT 2 - TIME: 16.3547478 s

method {:test} Test18() {
var r0, r1 := FindFirstRepeatedChar("\U{0003}\U{0007}\U{0005}\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0003}\U{0007}\U{0005}\U{0001}"| && "\U{0003}\U{0007}\U{0005}\U{0001}"[i] == "\U{0003}\U{0007}\U{0005}\U{0001}"[j] && "\U{0003}\U{0007}\U{0005}\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0003}\U{0007}\U{0005}\U{0001}"[k] == "\U{0003}\U{0007}\U{0005}\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0003}\U{0007}\U{0005}\U{0001}"| ==> "\U{0003}\U{0007}\U{0005}\U{0001}"[i] != "\U{0003}\U{0007}\U{0005}\U{0001}"[j];
}
method {:test} Test19() {
var r0, r1 := FindFirstRepeatedChar("\0a\U{0001}aa\0aaaaaaaaaaa\U{0004}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0a\U{0001}aa\0aaaaaaaaaaa\U{0004}"| && "\0a\U{0001}aa\0aaaaaaaaaaa\U{0004}"[i] == "\0a\U{0001}aa\0aaaaaaaaaaa\U{0004}"[j] && "\0a\U{0001}aa\0aaaaaaaaaaa\U{0004}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0a\U{0001}aa\0aaaaaaaaaaa\U{0004}"[k] == "\0a\U{0001}aa\0aaaaaaaaaaa\U{0004}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0a\U{0001}aa\0aaaaaaaaaaa\U{0004}"| ==> "\0a\U{0001}aa\0aaaaaaaaaaa\U{0004}"[i] != "\0a\U{0001}aa\0aaaaaaaaaaa\U{0004}"[j];
}

// REPEAT 3 - TIME: 17.6205071 s

method {:test} Test20() {
var r0, r1 := FindFirstRepeatedChar("\U{0005}\U{000B}\U{0007}aaaa\t\U{0001}\r\U{0003}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0005}\U{000B}\U{0007}aaaa\t\U{0001}\r\U{0003}"| && "\U{0005}\U{000B}\U{0007}aaaa\t\U{0001}\r\U{0003}"[i] == "\U{0005}\U{000B}\U{0007}aaaa\t\U{0001}\r\U{0003}"[j] && "\U{0005}\U{000B}\U{0007}aaaa\t\U{0001}\r\U{0003}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0005}\U{000B}\U{0007}aaaa\t\U{0001}\r\U{0003}"[k] == "\U{0005}\U{000B}\U{0007}aaaa\t\U{0001}\r\U{0003}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0005}\U{000B}\U{0007}aaaa\t\U{0001}\r\U{0003}"| ==> "\U{0005}\U{000B}\U{0007}aaaa\t\U{0001}\r\U{0003}"[i] != "\U{0005}\U{000B}\U{0007}aaaa\t\U{0001}\r\U{0003}"[j];
}
method {:test} Test21() {
var r0, r1 := FindFirstRepeatedChar("\0a\U{0002}aaaaa\U{0004}\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0a\U{0002}aaaaa\U{0004}\0"| && "\0a\U{0002}aaaaa\U{0004}\0"[i] == "\0a\U{0002}aaaaa\U{0004}\0"[j] && "\0a\U{0002}aaaaa\U{0004}\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0a\U{0002}aaaaa\U{0004}\0"[k] == "\0a\U{0002}aaaaa\U{0004}\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0a\U{0002}aaaaa\U{0004}\0"| ==> "\0a\U{0002}aaaaa\U{0004}\0"[i] != "\0a\U{0002}aaaaa\U{0004}\0"[j];
}

// REPEAT 4 - TIME: 19.1280319 s

method {:test} Test22() {
var r0, r1 := FindFirstRepeatedChar("\U{0003}aaaaa\U{0007}aaaaaaaaaaa\U{000F}\r\U{000B}\t\U{0005}\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0003}aaaaa\U{0007}aaaaaaaaaaa\U{000F}\r\U{000B}\t\U{0005}\U{0001}"| && "\U{0003}aaaaa\U{0007}aaaaaaaaaaa\U{000F}\r\U{000B}\t\U{0005}\U{0001}"[i] == "\U{0003}aaaaa\U{0007}aaaaaaaaaaa\U{000F}\r\U{000B}\t\U{0005}\U{0001}"[j] && "\U{0003}aaaaa\U{0007}aaaaaaaaaaa\U{000F}\r\U{000B}\t\U{0005}\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0003}aaaaa\U{0007}aaaaaaaaaaa\U{000F}\r\U{000B}\t\U{0005}\U{0001}"[k] == "\U{0003}aaaaa\U{0007}aaaaaaaaaaa\U{000F}\r\U{000B}\t\U{0005}\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0003}aaaaa\U{0007}aaaaaaaaaaa\U{000F}\r\U{000B}\t\U{0005}\U{0001}"| ==> "\U{0003}aaaaa\U{0007}aaaaaaaaaaa\U{000F}\r\U{000B}\t\U{0005}\U{0001}"[i] != "\U{0003}aaaaa\U{0007}aaaaaaaaaaa\U{000F}\r\U{000B}\t\U{0005}\U{0001}"[j];
}
method {:test} Test23() {
var r0, r1 := FindFirstRepeatedChar("a\0aaaa\U{0002}a\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"a\0aaaa\U{0002}a\0"| && "a\0aaaa\U{0002}a\0"[i] == "a\0aaaa\U{0002}a\0"[j] && "a\0aaaa\U{0002}a\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "a\0aaaa\U{0002}a\0"[k] == "a\0aaaa\U{0002}a\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"a\0aaaa\U{0002}a\0"| ==> "a\0aaaa\U{0002}a\0"[i] != "a\0aaaa\U{0002}a\0"[j];
}

// REPEAT 5 - TIME: 20.670357 s

method {:test} Test24() {
var r0, r1 := FindFirstRepeatedChar("\U{0003}aaaaaaaaaa\t\U{0005}aaaaa\U{000B}aaaa\U{0007}\U{000F}\r\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0003}aaaaaaaaaa\t\U{0005}aaaaa\U{000B}aaaa\U{0007}\U{000F}\r\U{0001}"| && "\U{0003}aaaaaaaaaa\t\U{0005}aaaaa\U{000B}aaaa\U{0007}\U{000F}\r\U{0001}"[i] == "\U{0003}aaaaaaaaaa\t\U{0005}aaaaa\U{000B}aaaa\U{0007}\U{000F}\r\U{0001}"[j] && "\U{0003}aaaaaaaaaa\t\U{0005}aaaaa\U{000B}aaaa\U{0007}\U{000F}\r\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0003}aaaaaaaaaa\t\U{0005}aaaaa\U{000B}aaaa\U{0007}\U{000F}\r\U{0001}"[k] == "\U{0003}aaaaaaaaaa\t\U{0005}aaaaa\U{000B}aaaa\U{0007}\U{000F}\r\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0003}aaaaaaaaaa\t\U{0005}aaaaa\U{000B}aaaa\U{0007}\U{000F}\r\U{0001}"| ==> "\U{0003}aaaaaaaaaa\t\U{0005}aaaaa\U{000B}aaaa\U{0007}\U{000F}\r\U{0001}"[i] != "\U{0003}aaaaaaaaaa\t\U{0005}aaaaa\U{000B}aaaa\U{0007}\U{000F}\r\U{0001}"[j];
}
method {:test} Test25() {
var r0, r1 := FindFirstRepeatedChar("a\0aaaa\U{000E}\U{0004}\0a\U{0008}aa\n\U{0006}aa\U{0002}\U{000C}");
expect r0 ==> exists i, j :: 0 <= i < j < |"a\0aaaa\U{000E}\U{0004}\0a\U{0008}aa\n\U{0006}aa\U{0002}\U{000C}"| && "a\0aaaa\U{000E}\U{0004}\0a\U{0008}aa\n\U{0006}aa\U{0002}\U{000C}"[i] == "a\0aaaa\U{000E}\U{0004}\0a\U{0008}aa\n\U{0006}aa\U{0002}\U{000C}"[j] && "a\0aaaa\U{000E}\U{0004}\0a\U{0008}aa\n\U{0006}aa\U{0002}\U{000C}"[i] == r1 && forall k, l :: 0 <= k < l < j && "a\0aaaa\U{000E}\U{0004}\0a\U{0008}aa\n\U{0006}aa\U{0002}\U{000C}"[k] == "a\0aaaa\U{000E}\U{0004}\0a\U{0008}aa\n\U{0006}aa\U{0002}\U{000C}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"a\0aaaa\U{000E}\U{0004}\0a\U{0008}aa\n\U{0006}aa\U{0002}\U{000C}"| ==> "a\0aaaa\U{000E}\U{0004}\0a\U{0008}aa\n\U{0006}aa\U{0002}\U{000C}"[i] != "a\0aaaa\U{000E}\U{0004}\0a\U{0008}aa\n\U{0006}aa\U{0002}\U{000C}"[j];
}

// REPEAT 6 - TIME: 22.3068496 s

method {:test} Test26() {
var r0, r1 := FindFirstRepeatedChar("\U{0007}aaaa\U{0017}aaaaaaaaaaaa\U{0013}a\ra\U{0003}\U{0001}\U{0015}\U{0011}\U{000F}\U{000B}\t\U{0005}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0007}aaaa\U{0017}aaaaaaaaaaaa\U{0013}a\ra\U{0003}\U{0001}\U{0015}\U{0011}\U{000F}\U{000B}\t\U{0005}"| && "\U{0007}aaaa\U{0017}aaaaaaaaaaaa\U{0013}a\ra\U{0003}\U{0001}\U{0015}\U{0011}\U{000F}\U{000B}\t\U{0005}"[i] == "\U{0007}aaaa\U{0017}aaaaaaaaaaaa\U{0013}a\ra\U{0003}\U{0001}\U{0015}\U{0011}\U{000F}\U{000B}\t\U{0005}"[j] && "\U{0007}aaaa\U{0017}aaaaaaaaaaaa\U{0013}a\ra\U{0003}\U{0001}\U{0015}\U{0011}\U{000F}\U{000B}\t\U{0005}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0007}aaaa\U{0017}aaaaaaaaaaaa\U{0013}a\ra\U{0003}\U{0001}\U{0015}\U{0011}\U{000F}\U{000B}\t\U{0005}"[k] == "\U{0007}aaaa\U{0017}aaaaaaaaaaaa\U{0013}a\ra\U{0003}\U{0001}\U{0015}\U{0011}\U{000F}\U{000B}\t\U{0005}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0007}aaaa\U{0017}aaaaaaaaaaaa\U{0013}a\ra\U{0003}\U{0001}\U{0015}\U{0011}\U{000F}\U{000B}\t\U{0005}"| ==> "\U{0007}aaaa\U{0017}aaaaaaaaaaaa\U{0013}a\ra\U{0003}\U{0001}\U{0015}\U{0011}\U{000F}\U{000B}\t\U{0005}"[i] != "\U{0007}aaaa\U{0017}aaaaaaaaaaaa\U{0013}a\ra\U{0003}\U{0001}\U{0015}\U{0011}\U{000F}\U{000B}\t\U{0005}"[j];
}
method {:test} Test27() {
var r0, r1 := FindFirstRepeatedChar("\0\U{0003}\U{0001}\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0\U{0003}\U{0001}\0"| && "\0\U{0003}\U{0001}\0"[i] == "\0\U{0003}\U{0001}\0"[j] && "\0\U{0003}\U{0001}\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0\U{0003}\U{0001}\0"[k] == "\0\U{0003}\U{0001}\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0\U{0003}\U{0001}\0"| ==> "\0\U{0003}\U{0001}\0"[i] != "\0\U{0003}\U{0001}\0"[j];
}

// REPEAT 7 - TIME: 24.1678733 s

method {:test} Test28() {
var r0, r1 := FindFirstRepeatedChar("\U{0003}aaaaaa\ra\U{000F}\U{000B}\U{0017}\U{0015}\U{0007}aa\U{0005}a\t\U{0013}\U{0011}a\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0003}aaaaaa\ra\U{000F}\U{000B}\U{0017}\U{0015}\U{0007}aa\U{0005}a\t\U{0013}\U{0011}a\U{0001}"| && "\U{0003}aaaaaa\ra\U{000F}\U{000B}\U{0017}\U{0015}\U{0007}aa\U{0005}a\t\U{0013}\U{0011}a\U{0001}"[i] == "\U{0003}aaaaaa\ra\U{000F}\U{000B}\U{0017}\U{0015}\U{0007}aa\U{0005}a\t\U{0013}\U{0011}a\U{0001}"[j] && "\U{0003}aaaaaa\ra\U{000F}\U{000B}\U{0017}\U{0015}\U{0007}aa\U{0005}a\t\U{0013}\U{0011}a\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0003}aaaaaa\ra\U{000F}\U{000B}\U{0017}\U{0015}\U{0007}aa\U{0005}a\t\U{0013}\U{0011}a\U{0001}"[k] == "\U{0003}aaaaaa\ra\U{000F}\U{000B}\U{0017}\U{0015}\U{0007}aa\U{0005}a\t\U{0013}\U{0011}a\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0003}aaaaaa\ra\U{000F}\U{000B}\U{0017}\U{0015}\U{0007}aa\U{0005}a\t\U{0013}\U{0011}a\U{0001}"| ==> "\U{0003}aaaaaa\ra\U{000F}\U{000B}\U{0017}\U{0015}\U{0007}aa\U{0005}a\t\U{0013}\U{0011}a\U{0001}"[i] != "\U{0003}aaaaaa\ra\U{000F}\U{000B}\U{0017}\U{0015}\U{0007}aa\U{0005}a\t\U{0013}\U{0011}a\U{0001}"[j];
}
method {:test} Test29() {
var r0, r1 := FindFirstRepeatedChar("aaaaa\0\U{0006}a\U{0004}a\0\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaa\0\U{0006}a\U{0004}a\0\U{0002}"| && "aaaaa\0\U{0006}a\U{0004}a\0\U{0002}"[i] == "aaaaa\0\U{0006}a\U{0004}a\0\U{0002}"[j] && "aaaaa\0\U{0006}a\U{0004}a\0\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaa\0\U{0006}a\U{0004}a\0\U{0002}"[k] == "aaaaa\0\U{0006}a\U{0004}a\0\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaa\0\U{0006}a\U{0004}a\0\U{0002}"| ==> "aaaaa\0\U{0006}a\U{0004}a\0\U{0002}"[i] != "aaaaa\0\U{0006}a\U{0004}a\0\U{0002}"[j];
}

// REPEAT 8 - TIME: 25.9007127 s

method {:test} Test30() {
var r0, r1 := FindFirstRepeatedChar("\U{0001}\U{0005}\U{0007}\U{0003}\ta");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0001}\U{0005}\U{0007}\U{0003}\ta"| && "\U{0001}\U{0005}\U{0007}\U{0003}\ta"[i] == "\U{0001}\U{0005}\U{0007}\U{0003}\ta"[j] && "\U{0001}\U{0005}\U{0007}\U{0003}\ta"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0001}\U{0005}\U{0007}\U{0003}\ta"[k] == "\U{0001}\U{0005}\U{0007}\U{0003}\ta"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0001}\U{0005}\U{0007}\U{0003}\ta"| ==> "\U{0001}\U{0005}\U{0007}\U{0003}\ta"[i] != "\U{0001}\U{0005}\U{0007}\U{0003}\ta"[j];
}
method {:test} Test31() {
var r0, r1 := FindFirstRepeatedChar("\0\U{0002}\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0\U{0002}\0"| && "\0\U{0002}\0"[i] == "\0\U{0002}\0"[j] && "\0\U{0002}\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0\U{0002}\0"[k] == "\0\U{0002}\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0\U{0002}\0"| ==> "\0\U{0002}\0"[i] != "\0\U{0002}\0"[j];
}

// REPEAT 9 - TIME: 28.3770357 s

method {:test} Test32() {
var r0, r1 := FindFirstRepeatedChar("\U{0015}\U{0017}\U{0019}a\U{000B}\U{001D}\U{001B}aaaaaaaa\U{0011}aa\U{0013}\U{000F}\ra\ta\U{0003}\U{0007}\U{0005}\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0015}\U{0017}\U{0019}a\U{000B}\U{001D}\U{001B}aaaaaaaa\U{0011}aa\U{0013}\U{000F}\ra\ta\U{0003}\U{0007}\U{0005}\U{0001}"| && "\U{0015}\U{0017}\U{0019}a\U{000B}\U{001D}\U{001B}aaaaaaaa\U{0011}aa\U{0013}\U{000F}\ra\ta\U{0003}\U{0007}\U{0005}\U{0001}"[i] == "\U{0015}\U{0017}\U{0019}a\U{000B}\U{001D}\U{001B}aaaaaaaa\U{0011}aa\U{0013}\U{000F}\ra\ta\U{0003}\U{0007}\U{0005}\U{0001}"[j] && "\U{0015}\U{0017}\U{0019}a\U{000B}\U{001D}\U{001B}aaaaaaaa\U{0011}aa\U{0013}\U{000F}\ra\ta\U{0003}\U{0007}\U{0005}\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0015}\U{0017}\U{0019}a\U{000B}\U{001D}\U{001B}aaaaaaaa\U{0011}aa\U{0013}\U{000F}\ra\ta\U{0003}\U{0007}\U{0005}\U{0001}"[k] == "\U{0015}\U{0017}\U{0019}a\U{000B}\U{001D}\U{001B}aaaaaaaa\U{0011}aa\U{0013}\U{000F}\ra\ta\U{0003}\U{0007}\U{0005}\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0015}\U{0017}\U{0019}a\U{000B}\U{001D}\U{001B}aaaaaaaa\U{0011}aa\U{0013}\U{000F}\ra\ta\U{0003}\U{0007}\U{0005}\U{0001}"| ==> "\U{0015}\U{0017}\U{0019}a\U{000B}\U{001D}\U{001B}aaaaaaaa\U{0011}aa\U{0013}\U{000F}\ra\ta\U{0003}\U{0007}\U{0005}\U{0001}"[i] != "\U{0015}\U{0017}\U{0019}a\U{000B}\U{001D}\U{001B}aaaaaaaa\U{0011}aa\U{0013}\U{000F}\ra\ta\U{0003}\U{0007}\U{0005}\U{0001}"[j];
}
method {:test} Test33() {
var r0, r1 := FindFirstRepeatedChar("a\0aaaa\U{0012}\U{0004}aa\0\U{0008}aaa\naa\U{000C}a\U{000E}a\U{0006}a\U{0010}\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"a\0aaaa\U{0012}\U{0004}aa\0\U{0008}aaa\naa\U{000C}a\U{000E}a\U{0006}a\U{0010}\U{0002}"| && "a\0aaaa\U{0012}\U{0004}aa\0\U{0008}aaa\naa\U{000C}a\U{000E}a\U{0006}a\U{0010}\U{0002}"[i] == "a\0aaaa\U{0012}\U{0004}aa\0\U{0008}aaa\naa\U{000C}a\U{000E}a\U{0006}a\U{0010}\U{0002}"[j] && "a\0aaaa\U{0012}\U{0004}aa\0\U{0008}aaa\naa\U{000C}a\U{000E}a\U{0006}a\U{0010}\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "a\0aaaa\U{0012}\U{0004}aa\0\U{0008}aaa\naa\U{000C}a\U{000E}a\U{0006}a\U{0010}\U{0002}"[k] == "a\0aaaa\U{0012}\U{0004}aa\0\U{0008}aaa\naa\U{000C}a\U{000E}a\U{0006}a\U{0010}\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"a\0aaaa\U{0012}\U{0004}aa\0\U{0008}aaa\naa\U{000C}a\U{000E}a\U{0006}a\U{0010}\U{0002}"| ==> "a\0aaaa\U{0012}\U{0004}aa\0\U{0008}aaa\naa\U{000C}a\U{000E}a\U{0006}a\U{0010}\U{0002}"[i] != "a\0aaaa\U{0012}\U{0004}aa\0\U{0008}aaa\naa\U{000C}a\U{000E}a\U{0006}a\U{0010}\U{0002}"[j];
}

// REPEAT 10 - TIME: 30.0535604 s
