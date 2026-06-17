// dafny-synthesis_task_id_454.dfy

method {:testEntry} ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
  {
    if s[i] == 'z' ==> s[i] == 'Z' {
      result := true;
      break;
    }
  }
}

method {:test} Test4() {
var r0 := ContainsZ("Zaa\U{0006}aaa\0aaaaaaaaaaaa\U{0002}\U{0004}aa");
expect r0 <==> exists i :: 0 <= i < |"Zaa\U{0006}aaa\0aaaaaaaaaaaa\U{0002}\U{0004}aa"| && ("Zaa\U{0006}aaa\0aaaaaaaaaaaa\U{0002}\U{0004}aa"[i] == 'z' || "Zaa\U{0006}aaa\0aaaaaaaaaaaa\U{0002}\U{0004}aa"[i] == 'Z');
}
method {:test} Test5() {
var r0 := ContainsZ("az\U{0001}aa");
expect r0 <==> exists i :: 0 <= i < |"az\U{0001}aa"| && ("az\U{0001}aa"[i] == 'z' || "az\U{0001}aa"[i] == 'Z');
}

// REPEAT 3 - TIME: 5.4324198 s
