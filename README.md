BitMasks Sets
=============

Library for exposing bitmasks (typically as `int` or `int64`) in an implementation compatible with
OCaml's `Set`. The underlying data representation is unaltered, allowing the value to be manipulated
either as a bitmask or as a set without conversion.

Dependencies
------------

This library uses the [oasis](https://github.com/ocaml/oasis) architecture which is necessary to
compile the build system from the repository. Release tarballs include the build system.
