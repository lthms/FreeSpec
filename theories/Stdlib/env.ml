open Coqbase

let getenv name =
  try
    let res = Unix.getenv (Bytestring.to_string name) in
    Some (Bytestring.of_string res)
  with
  | _ -> None

let setenv name value =
  Unix.putenv (Bytestring.to_string name) (Bytestring.to_string value)
