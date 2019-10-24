From FreeSpec Require Export Core Exec.
From FreeSpec Require Import Core.Notations.
From FreeSpec.Stdlib Require Export Raise.
From Coq Require Export String Int63.

#[local] Close Scope nat_scope.

Generalizable All Variables.

Axiom file_descriptor : Type.

Inductive files_err := make_files_err (code : int).

Inductive FILES : interface :=
| Open (path : string) : FILES (files_err + file_descriptor)
| FSize (fd : file_descriptor) : FILES (files_err + int)
| Read (fd : file_descriptor) (size : int) : FILES (files_err + (int * string))
| Close (fd : file_descriptor) : FILES unit.

Definition open `{Provide ix FILES} (path : string)
  : impure ix (files_err + file_descriptor) :=
  request (Open path).

Definition try_open `{Into files_err err, Provide2 ix (RAISE err) FILES} (path : string)
  : impure ix file_descriptor :=
  try (open path).

Definition file_size `{Provide ix FILES} (fd : file_descriptor)
  : impure ix (files_err + int) :=
  request (FSize fd).

Definition try_file_size `{Into files_err err, Provide2 ix (RAISE err) FILES}
    (fd : file_descriptor)
  : impure ix int :=
  try (file_size fd).

Definition read `{Provide ix FILES} (fd : file_descriptor) (size : int)
  : impure ix (files_err + (int * string)) :=
  request (Read fd size).

Definition try_read `{Into files_err err, Provide2 ix (RAISE err) FILES}
    (fd : file_descriptor) (size : int)
  : impure ix (int * string) :=
  try (request (Read fd size)).

Definition close `{Provide ix FILES} (fd : file_descriptor)
  : impure ix unit :=
  request (Close fd).

Register file_descriptor as freespec.stdlib.file_descriptor.type.
Register files_err as freespec.stdlib.files_err.type.
Register make_files_err as freespec.stdlib.files_err.make_files_err.
Register FILES as freespec.stdlib.files.type.
Register Open as freespec.stdlib.files.Open.
Register Close as freespec.stdlib.files.Close.
Register Read as freespec.stdlib.files.Read.
Register FSize as freespec.stdlib.files.FSize.

Declare ML Module "freespec_stdlib_files".
