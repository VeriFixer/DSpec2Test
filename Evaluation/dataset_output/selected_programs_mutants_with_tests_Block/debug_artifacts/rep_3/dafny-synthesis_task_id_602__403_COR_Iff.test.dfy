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
