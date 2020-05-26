open Coqbase
open Coqbase.Sum

type file_descriptor = Unix.file_descr

type file_err = FileErr of int

type file_flag =
  | O_RDONLY
  | O_WRONLY
  | O_RDWR

let stdin = Unix.stdin
let stdout = Unix.stdin

let openfile path =
  try
    Inr (Unix.openfile (Bytestring.to_string path) [Unix.O_RDONLY] 0o640)
  with
    _ -> Inl (FileErr 1)

let read fd b = Inr (Bytestring.read fd b)

let read_line fd =
  let c = Unix.in_channel_of_descr fd in
  Inr (Bytestring.of_string (input_line c))

let fsize fd = Inr (Unix.fstat fd).st_size

let write fd b ofs len = Inr (Bytestring.write fd b ofs len)

let close fd = Inr (Unix.close fd)
