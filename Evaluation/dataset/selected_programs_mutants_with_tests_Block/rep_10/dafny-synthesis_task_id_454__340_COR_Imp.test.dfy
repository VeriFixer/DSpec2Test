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

method {:test} Test18() {
var r0 := ContainsZ("\0aaZaaa");
expect r0 <==> exists i :: 0 <= i < |"\0aaZaaa"| && ("\0aaZaaa"[i] == 'z' || "\0aaZaaa"[i] == 'Z');
}
method {:test} Test19() {
var r0 := ContainsZ("\U{0001}z");
expect r0 <==> exists i :: 0 <= i < |"\U{0001}z"| && ("\U{0001}z"[i] == 'z' || "\U{0001}z"[i] == 'Z');
}

// REPEAT 10 - TIME: 15.3991408 s
