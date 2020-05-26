open Coqbase

type file_descriptor

type file_err = FileErr of int

type file_flag =
  | O_RDONLY
  | O_WRONLY
  | O_RDWR

val stdin : file_descriptor
val stdout : file_descriptor

val openfile : Bytestring.t -> (file_err, file_descriptor) Sum.t [@@impure]
val read : file_descriptor -> int -> (file_err, Bytestring.t) Sum.t [@@impure]
val read_line : file_descriptor -> (file_err, Bytestring.t) Sum.t [@@impure]
val fsize : file_descriptor -> (file_err, int) Sum.t [@@impure]
val write : file_descriptor -> Bytestring.t -> int -> int -> (file_err, int) Sum.t [@@impure]
val close : file_descriptor -> (file_err, unit) Sum.t [@@impure]
