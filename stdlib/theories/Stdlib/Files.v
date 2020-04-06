From FreeSpec Require Export Core Exec.
From FreeSpec.Stdlib Require Export Raise.
From Coq Require Export Int63.
From Prelude Require Import Text Bytes.

Axiom file_descriptor : Type.

Inductive files_err := make_files_err (code : int).

Inductive FILES : Type -> Type :=
| Open (path : bytes) : FILES (files_err + file_descriptor)
| FSize (fd : file_descriptor) : FILES (files_err + int)
| Read (fd : file_descriptor) (size : int) : FILES (files_err + (int * bytes))
| Close (fd : file_descriptor) : FILES unit.

Definition open `{ix :| FILES} (path : bytes)
  : impure ix (files_err + file_descriptor) :=
  request (Open path).

Definition try_open `{Into files_err err, ix :| RAISE err, FILES} (path : bytes)
  : impure ix file_descriptor :=
  try (open path).

Definition file_size `{ix :| FILES} (fd : file_descriptor)
  : impure ix (files_err + int) :=
  request (FSize fd).

Definition try_file_size `{Into files_err err, ix :| RAISE err, FILES}
    (fd : file_descriptor)
  : impure ix int :=
  try (file_size fd).

Definition read `{ix :| FILES} (fd : file_descriptor) (size : int)
  : impure ix (files_err + (int * bytes)) :=
  request (Read fd size).

Definition try_read `{Into files_err err, ix :| RAISE err, FILES}
    (fd : file_descriptor) (size : int)
  : impure ix (int * bytes) :=
  try (request (Read fd size)).

Definition close `{ix :| FILES} (fd : file_descriptor)
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
