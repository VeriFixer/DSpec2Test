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
