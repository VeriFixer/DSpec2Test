// dafny-synthesis_task_id_454.dfy

method {:testEntry} ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
  {
    if s[i] == 'Z' {
      result := true;
      break;
    }
  }
}

method {:test} Test27() {
var r0 := ContainsZ("\U{0002}a\0");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}a\0"| && ("\U{0002}a\0"[i] == 'z' || "\U{0002}a\0"[i] == 'Z');
}
method {:test} Test28() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaZ");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaZ"| && ("aaaaaaaaaaaaaaaaaaaaaZ"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaZ"[i] == 'Z');
}

// REPEAT 10 - TIME: 846.6362174 s
