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

// REPEAT 1 - TIME: 11.1925149 s

method {:test} Test16() {
var r0, r1 := FindFirstRepeatedChar("\U{0003}aaaaaaaaaaa\U{0005}\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0003}aaaaaaaaaaa\U{0005}\U{0001}"| && "\U{0003}aaaaaaaaaaa\U{0005}\U{0001}"[i] == "\U{0003}aaaaaaaaaaa\U{0005}\U{0001}"[j] && "\U{0003}aaaaaaaaaaa\U{0005}\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0003}aaaaaaaaaaa\U{0005}\U{0001}"[k] == "\U{0003}aaaaaaaaaaa\U{0005}\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0003}aaaaaaaaaaa\U{0005}\U{0001}"| ==> "\U{0003}aaaaaaaaaaa\U{0005}\U{0001}"[i] != "\U{0003}aaaaaaaaaaa\U{0005}\U{0001}"[j];
}
method {:test} Test17() {
var r0, r1 := FindFirstRepeatedChar("aaaaa\0\0\U{0006}aaaaa\U{0002}aaaaaaaaaaa\U{0004}");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaa\0\0\U{0006}aaaaa\U{0002}aaaaaaaaaaa\U{0004}"| && "aaaaa\0\0\U{0006}aaaaa\U{0002}aaaaaaaaaaa\U{0004}"[i] == "aaaaa\0\0\U{0006}aaaaa\U{0002}aaaaaaaaaaa\U{0004}"[j] && "aaaaa\0\0\U{0006}aaaaa\U{0002}aaaaaaaaaaa\U{0004}"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaa\0\0\U{0006}aaaaa\U{0002}aaaaaaaaaaa\U{0004}"[k] == "aaaaa\0\0\U{0006}aaaaa\U{0002}aaaaaaaaaaa\U{0004}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaa\0\0\U{0006}aaaaa\U{0002}aaaaaaaaaaa\U{0004}"| ==> "aaaaa\0\0\U{0006}aaaaa\U{0002}aaaaaaaaaaa\U{0004}"[i] != "aaaaa\0\0\U{0006}aaaaa\U{0002}aaaaaaaaaaa\U{0004}"[j];
}

// REPEAT 2 - TIME: 12.2722475 s

method {:test} Test18() {
var r0, r1 := FindFirstRepeatedChar("\U{0005}aa\U{0003}aaa\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0005}aa\U{0003}aaa\U{0001}"| && "\U{0005}aa\U{0003}aaa\U{0001}"[i] == "\U{0005}aa\U{0003}aaa\U{0001}"[j] && "\U{0005}aa\U{0003}aaa\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0005}aa\U{0003}aaa\U{0001}"[k] == "\U{0005}aa\U{0003}aaa\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0005}aa\U{0003}aaa\U{0001}"| ==> "\U{0005}aa\U{0003}aaa\U{0001}"[i] != "\U{0005}aa\U{0003}aaa\U{0001}"[j];
}
method {:test} Test19() {
var r0, r1 := FindFirstRepeatedChar("\0a\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0a\0"| && "\0a\0"[i] == "\0a\0"[j] && "\0a\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0a\0"[k] == "\0a\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0a\0"| ==> "\0a\0"[i] != "\0a\0"[j];
}

// REPEAT 3 - TIME: 13.3042392 s

method {:test} Test20() {
var r0, r1 := FindFirstRepeatedChar("\r\ta\U{0007}\U{000F}a\U{0005}\U{0001}\U{000B}\U{0003}\U{0011}aa");
expect r0 ==> exists i, j :: 0 <= i < j < |"\r\ta\U{0007}\U{000F}a\U{0005}\U{0001}\U{000B}\U{0003}\U{0011}aa"| && "\r\ta\U{0007}\U{000F}a\U{0005}\U{0001}\U{000B}\U{0003}\U{0011}aa"[i] == "\r\ta\U{0007}\U{000F}a\U{0005}\U{0001}\U{000B}\U{0003}\U{0011}aa"[j] && "\r\ta\U{0007}\U{000F}a\U{0005}\U{0001}\U{000B}\U{0003}\U{0011}aa"[i] == r1 && forall k, l :: 0 <= k < l < j && "\r\ta\U{0007}\U{000F}a\U{0005}\U{0001}\U{000B}\U{0003}\U{0011}aa"[k] == "\r\ta\U{0007}\U{000F}a\U{0005}\U{0001}\U{000B}\U{0003}\U{0011}aa"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\r\ta\U{0007}\U{000F}a\U{0005}\U{0001}\U{000B}\U{0003}\U{0011}aa"| ==> "\r\ta\U{0007}\U{000F}a\U{0005}\U{0001}\U{000B}\U{0003}\U{0011}aa"[i] != "\r\ta\U{0007}\U{000F}a\U{0005}\U{0001}\U{000B}\U{0003}\U{0011}aa"[j];
}
method {:test} Test21() {
var r0, r1 := FindFirstRepeatedChar("\0aaaaaa\U{0004}\U{0006}aaaaa\U{0008}aaaaaaaa\0a\n\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0aaaaaa\U{0004}\U{0006}aaaaa\U{0008}aaaaaaaa\0a\n\U{0002}"| && "\0aaaaaa\U{0004}\U{0006}aaaaa\U{0008}aaaaaaaa\0a\n\U{0002}"[i] == "\0aaaaaa\U{0004}\U{0006}aaaaa\U{0008}aaaaaaaa\0a\n\U{0002}"[j] && "\0aaaaaa\U{0004}\U{0006}aaaaa\U{0008}aaaaaaaa\0a\n\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0aaaaaa\U{0004}\U{0006}aaaaa\U{0008}aaaaaaaa\0a\n\U{0002}"[k] == "\0aaaaaa\U{0004}\U{0006}aaaaa\U{0008}aaaaaaaa\0a\n\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0aaaaaa\U{0004}\U{0006}aaaaa\U{0008}aaaaaaaa\0a\n\U{0002}"| ==> "\0aaaaaa\U{0004}\U{0006}aaaaa\U{0008}aaaaaaaa\0a\n\U{0002}"[i] != "\0aaaaaa\U{0004}\U{0006}aaaaa\U{0008}aaaaaaaa\0a\n\U{0002}"[j];
}

// REPEAT 4 - TIME: 14.5980245 s

method {:test} Test22() {
var r0, r1 := FindFirstRepeatedChar("\t\U{0007}a\U{0005}\U{0003}\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\t\U{0007}a\U{0005}\U{0003}\U{0001}"| && "\t\U{0007}a\U{0005}\U{0003}\U{0001}"[i] == "\t\U{0007}a\U{0005}\U{0003}\U{0001}"[j] && "\t\U{0007}a\U{0005}\U{0003}\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\t\U{0007}a\U{0005}\U{0003}\U{0001}"[k] == "\t\U{0007}a\U{0005}\U{0003}\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\t\U{0007}a\U{0005}\U{0003}\U{0001}"| ==> "\t\U{0007}a\U{0005}\U{0003}\U{0001}"[i] != "\t\U{0007}a\U{0005}\U{0003}\U{0001}"[j];
}
method {:test} Test23() {
var r0, r1 := FindFirstRepeatedChar("\0\U{0002}aaaaa\0\U{0004}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0\U{0002}aaaaa\0\U{0004}"| && "\0\U{0002}aaaaa\0\U{0004}"[i] == "\0\U{0002}aaaaa\0\U{0004}"[j] && "\0\U{0002}aaaaa\0\U{0004}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0\U{0002}aaaaa\0\U{0004}"[k] == "\0\U{0002}aaaaa\0\U{0004}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0\U{0002}aaaaa\0\U{0004}"| ==> "\0\U{0002}aaaaa\0\U{0004}"[i] != "\0\U{0002}aaaaa\0\U{0004}"[j];
}

// REPEAT 5 - TIME: 15.7950145 s

method {:test} Test24() {
var r0, r1 := FindFirstRepeatedChar("\t\U{0005}\U{0001}\U{0003}a\U{0007}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\t\U{0005}\U{0001}\U{0003}a\U{0007}"| && "\t\U{0005}\U{0001}\U{0003}a\U{0007}"[i] == "\t\U{0005}\U{0001}\U{0003}a\U{0007}"[j] && "\t\U{0005}\U{0001}\U{0003}a\U{0007}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\t\U{0005}\U{0001}\U{0003}a\U{0007}"[k] == "\t\U{0005}\U{0001}\U{0003}a\U{0007}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\t\U{0005}\U{0001}\U{0003}a\U{0007}"| ==> "\t\U{0005}\U{0001}\U{0003}a\U{0007}"[i] != "\t\U{0005}\U{0001}\U{0003}a\U{0007}"[j];
}
method {:test} Test25() {
var r0, r1 := FindFirstRepeatedChar("\0aaaaa\U{000C}\U{0002}\U{0006}a\U{0008}a\U{0004}a\naaaa\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0aaaaa\U{000C}\U{0002}\U{0006}a\U{0008}a\U{0004}a\naaaa\0"| && "\0aaaaa\U{000C}\U{0002}\U{0006}a\U{0008}a\U{0004}a\naaaa\0"[i] == "\0aaaaa\U{000C}\U{0002}\U{0006}a\U{0008}a\U{0004}a\naaaa\0"[j] && "\0aaaaa\U{000C}\U{0002}\U{0006}a\U{0008}a\U{0004}a\naaaa\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0aaaaa\U{000C}\U{0002}\U{0006}a\U{0008}a\U{0004}a\naaaa\0"[k] == "\0aaaaa\U{000C}\U{0002}\U{0006}a\U{0008}a\U{0004}a\naaaa\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0aaaaa\U{000C}\U{0002}\U{0006}a\U{0008}a\U{0004}a\naaaa\0"| ==> "\0aaaaa\U{000C}\U{0002}\U{0006}a\U{0008}a\U{0004}a\naaaa\0"[i] != "\0aaaaa\U{000C}\U{0002}\U{0006}a\U{0008}a\U{0004}a\naaaa\0"[j];
}

// REPEAT 6 - TIME: 17.0435255 s

method {:test} Test26() {
var r0, r1 := FindFirstRepeatedChar("\U{000B}\r\U{000F}\U{0011}\U{0013}\U{0007}\taa\U{0005}\U{0003}a\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{000B}\r\U{000F}\U{0011}\U{0013}\U{0007}\taa\U{0005}\U{0003}a\U{0001}"| && "\U{000B}\r\U{000F}\U{0011}\U{0013}\U{0007}\taa\U{0005}\U{0003}a\U{0001}"[i] == "\U{000B}\r\U{000F}\U{0011}\U{0013}\U{0007}\taa\U{0005}\U{0003}a\U{0001}"[j] && "\U{000B}\r\U{000F}\U{0011}\U{0013}\U{0007}\taa\U{0005}\U{0003}a\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{000B}\r\U{000F}\U{0011}\U{0013}\U{0007}\taa\U{0005}\U{0003}a\U{0001}"[k] == "\U{000B}\r\U{000F}\U{0011}\U{0013}\U{0007}\taa\U{0005}\U{0003}a\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{000B}\r\U{000F}\U{0011}\U{0013}\U{0007}\taa\U{0005}\U{0003}a\U{0001}"| ==> "\U{000B}\r\U{000F}\U{0011}\U{0013}\U{0007}\taa\U{0005}\U{0003}a\U{0001}"[i] != "\U{000B}\r\U{000F}\U{0011}\U{0013}\U{0007}\taa\U{0005}\U{0003}a\U{0001}"[j];
}
method {:test} Test27() {
var r0, r1 := FindFirstRepeatedChar("\0\U{0008}\U{000E}\U{0010}a\U{0006}\n\U{000C}\U{0003}\U{0001}\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0\U{0008}\U{000E}\U{0010}a\U{0006}\n\U{000C}\U{0003}\U{0001}\0"| && "\0\U{0008}\U{000E}\U{0010}a\U{0006}\n\U{000C}\U{0003}\U{0001}\0"[i] == "\0\U{0008}\U{000E}\U{0010}a\U{0006}\n\U{000C}\U{0003}\U{0001}\0"[j] && "\0\U{0008}\U{000E}\U{0010}a\U{0006}\n\U{000C}\U{0003}\U{0001}\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0\U{0008}\U{000E}\U{0010}a\U{0006}\n\U{000C}\U{0003}\U{0001}\0"[k] == "\0\U{0008}\U{000E}\U{0010}a\U{0006}\n\U{000C}\U{0003}\U{0001}\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0\U{0008}\U{000E}\U{0010}a\U{0006}\n\U{000C}\U{0003}\U{0001}\0"| ==> "\0\U{0008}\U{000E}\U{0010}a\U{0006}\n\U{000C}\U{0003}\U{0001}\0"[i] != "\0\U{0008}\U{000E}\U{0010}a\U{0006}\n\U{000C}\U{0003}\U{0001}\0"[j];
}

// REPEAT 7 - TIME: 18.2122421 s

method {:test} Test28() {
var r0, r1 := FindFirstRepeatedChar("\U{0007}\U{0005}\U{0001}\U{000B}\t\U{0003}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0007}\U{0005}\U{0001}\U{000B}\t\U{0003}"| && "\U{0007}\U{0005}\U{0001}\U{000B}\t\U{0003}"[i] == "\U{0007}\U{0005}\U{0001}\U{000B}\t\U{0003}"[j] && "\U{0007}\U{0005}\U{0001}\U{000B}\t\U{0003}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0007}\U{0005}\U{0001}\U{000B}\t\U{0003}"[k] == "\U{0007}\U{0005}\U{0001}\U{000B}\t\U{0003}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0007}\U{0005}\U{0001}\U{000B}\t\U{0003}"| ==> "\U{0007}\U{0005}\U{0001}\U{000B}\t\U{0003}"[i] != "\U{0007}\U{0005}\U{0001}\U{000B}\t\U{0003}"[j];
}
method {:test} Test29() {
var r0, r1 := FindFirstRepeatedChar("\0\U{0006}\U{0002}\U{0004}\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0\U{0006}\U{0002}\U{0004}\0"| && "\0\U{0006}\U{0002}\U{0004}\0"[i] == "\0\U{0006}\U{0002}\U{0004}\0"[j] && "\0\U{0006}\U{0002}\U{0004}\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0\U{0006}\U{0002}\U{0004}\0"[k] == "\0\U{0006}\U{0002}\U{0004}\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0\U{0006}\U{0002}\U{0004}\0"| ==> "\0\U{0006}\U{0002}\U{0004}\0"[i] != "\0\U{0006}\U{0002}\U{0004}\0"[j];
}

// REPEAT 8 - TIME: 19.5907147 s

method {:test} Test30() {
var r0, r1 := FindFirstRepeatedChar("\U{0011}\U{0007}a\U{000F}\U{0005}\U{0001}\r\t\U{000B}\U{0003}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0011}\U{0007}a\U{000F}\U{0005}\U{0001}\r\t\U{000B}\U{0003}"| && "\U{0011}\U{0007}a\U{000F}\U{0005}\U{0001}\r\t\U{000B}\U{0003}"[i] == "\U{0011}\U{0007}a\U{000F}\U{0005}\U{0001}\r\t\U{000B}\U{0003}"[j] && "\U{0011}\U{0007}a\U{000F}\U{0005}\U{0001}\r\t\U{000B}\U{0003}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0011}\U{0007}a\U{000F}\U{0005}\U{0001}\r\t\U{000B}\U{0003}"[k] == "\U{0011}\U{0007}a\U{000F}\U{0005}\U{0001}\r\t\U{000B}\U{0003}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0011}\U{0007}a\U{000F}\U{0005}\U{0001}\r\t\U{000B}\U{0003}"| ==> "\U{0011}\U{0007}a\U{000F}\U{0005}\U{0001}\r\t\U{000B}\U{0003}"[i] != "\U{0011}\U{0007}a\U{000F}\U{0005}\U{0001}\r\t\U{000B}\U{0003}"[j];
}
method {:test} Test31() {
var r0, r1 := FindFirstRepeatedChar("a\0\0aaaaaaa\U{0002}\U{0006}aaa\U{0004}aa\na\U{000C}aaaa\U{000E}\U{0010}\U{0008}");
expect r0 ==> exists i, j :: 0 <= i < j < |"a\0\0aaaaaaa\U{0002}\U{0006}aaa\U{0004}aa\na\U{000C}aaaa\U{000E}\U{0010}\U{0008}"| && "a\0\0aaaaaaa\U{0002}\U{0006}aaa\U{0004}aa\na\U{000C}aaaa\U{000E}\U{0010}\U{0008}"[i] == "a\0\0aaaaaaa\U{0002}\U{0006}aaa\U{0004}aa\na\U{000C}aaaa\U{000E}\U{0010}\U{0008}"[j] && "a\0\0aaaaaaa\U{0002}\U{0006}aaa\U{0004}aa\na\U{000C}aaaa\U{000E}\U{0010}\U{0008}"[i] == r1 && forall k, l :: 0 <= k < l < j && "a\0\0aaaaaaa\U{0002}\U{0006}aaa\U{0004}aa\na\U{000C}aaaa\U{000E}\U{0010}\U{0008}"[k] == "a\0\0aaaaaaa\U{0002}\U{0006}aaa\U{0004}aa\na\U{000C}aaaa\U{000E}\U{0010}\U{0008}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"a\0\0aaaaaaa\U{0002}\U{0006}aaa\U{0004}aa\na\U{000C}aaaa\U{000E}\U{0010}\U{0008}"| ==> "a\0\0aaaaaaa\U{0002}\U{0006}aaa\U{0004}aa\na\U{000C}aaaa\U{000E}\U{0010}\U{0008}"[i] != "a\0\0aaaaaaa\U{0002}\U{0006}aaa\U{0004}aa\na\U{000C}aaaa\U{000E}\U{0010}\U{0008}"[j];
}

// REPEAT 9 - TIME: 21.0067352 s

method {:test} Test32() {
var r0, r1 := FindFirstRepeatedChar("\U{0013}\U{0011}aaaaaaaaaaaaa\raaaa\U{000F}\U{000B}\t\U{0007}\U{0005}\U{0001}\U{0003}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0013}\U{0011}aaaaaaaaaaaaa\raaaa\U{000F}\U{000B}\t\U{0007}\U{0005}\U{0001}\U{0003}"| && "\U{0013}\U{0011}aaaaaaaaaaaaa\raaaa\U{000F}\U{000B}\t\U{0007}\U{0005}\U{0001}\U{0003}"[i] == "\U{0013}\U{0011}aaaaaaaaaaaaa\raaaa\U{000F}\U{000B}\t\U{0007}\U{0005}\U{0001}\U{0003}"[j] && "\U{0013}\U{0011}aaaaaaaaaaaaa\raaaa\U{000F}\U{000B}\t\U{0007}\U{0005}\U{0001}\U{0003}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0013}\U{0011}aaaaaaaaaaaaa\raaaa\U{000F}\U{000B}\t\U{0007}\U{0005}\U{0001}\U{0003}"[k] == "\U{0013}\U{0011}aaaaaaaaaaaaa\raaaa\U{000F}\U{000B}\t\U{0007}\U{0005}\U{0001}\U{0003}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0013}\U{0011}aaaaaaaaaaaaa\raaaa\U{000F}\U{000B}\t\U{0007}\U{0005}\U{0001}\U{0003}"| ==> "\U{0013}\U{0011}aaaaaaaaaaaaa\raaaa\U{000F}\U{000B}\t\U{0007}\U{0005}\U{0001}\U{0003}"[i] != "\U{0013}\U{0011}aaaaaaaaaaaaa\raaaa\U{000F}\U{000B}\t\U{0007}\U{0005}\U{0001}\U{0003}"[j];
}
method {:test} Test33() {
var r0, r1 := FindFirstRepeatedChar("a\0\0aa\U{0008}\naaaaaaaa\U{0002}aa\U{0010}\U{0012}\U{0004}a\U{0006}a\U{000E}\U{0014}\U{0016}\U{0018}\U{000C}");
expect r0 ==> exists i, j :: 0 <= i < j < |"a\0\0aa\U{0008}\naaaaaaaa\U{0002}aa\U{0010}\U{0012}\U{0004}a\U{0006}a\U{000E}\U{0014}\U{0016}\U{0018}\U{000C}"| && "a\0\0aa\U{0008}\naaaaaaaa\U{0002}aa\U{0010}\U{0012}\U{0004}a\U{0006}a\U{000E}\U{0014}\U{0016}\U{0018}\U{000C}"[i] == "a\0\0aa\U{0008}\naaaaaaaa\U{0002}aa\U{0010}\U{0012}\U{0004}a\U{0006}a\U{000E}\U{0014}\U{0016}\U{0018}\U{000C}"[j] && "a\0\0aa\U{0008}\naaaaaaaa\U{0002}aa\U{0010}\U{0012}\U{0004}a\U{0006}a\U{000E}\U{0014}\U{0016}\U{0018}\U{000C}"[i] == r1 && forall k, l :: 0 <= k < l < j && "a\0\0aa\U{0008}\naaaaaaaa\U{0002}aa\U{0010}\U{0012}\U{0004}a\U{0006}a\U{000E}\U{0014}\U{0016}\U{0018}\U{000C}"[k] == "a\0\0aa\U{0008}\naaaaaaaa\U{0002}aa\U{0010}\U{0012}\U{0004}a\U{0006}a\U{000E}\U{0014}\U{0016}\U{0018}\U{000C}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"a\0\0aa\U{0008}\naaaaaaaa\U{0002}aa\U{0010}\U{0012}\U{0004}a\U{0006}a\U{000E}\U{0014}\U{0016}\U{0018}\U{000C}"| ==> "a\0\0aa\U{0008}\naaaaaaaa\U{0002}aa\U{0010}\U{0012}\U{0004}a\U{0006}a\U{000E}\U{0014}\U{0016}\U{0018}\U{000C}"[i] != "a\0\0aa\U{0008}\naaaaaaaa\U{0002}aa\U{0010}\U{0012}\U{0004}a\U{0006}a\U{000E}\U{0014}\U{0016}\U{0018}\U{000C}"[j];
}

// REPEAT 10 - TIME: 22.2992781 s
