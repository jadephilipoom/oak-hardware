(****************************************************************************)
(* Copyright 2019 The Project Oak Authors                                   *)
(*                                                                          *)
(* Licensed under the Apache License, Version 2.0 (the "License")           *)
(* you may not use this file except in compliance with the License.         *)
(* You may obtain a copy of the License at                                  *)
(*                                                                          *)
(*     http://www.apache.org/licenses/LICENSE-2.0                           *)
(*                                                                          *)
(* Unless required by applicable law or agreed to in writing, software      *)
(* distributed under the License is distributed on an "AS IS" BASIS,        *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. *)
(* See the License for the specific language governing permissions and      *)
(* limitations under the License.                                           *)
(****************************************************************************)

Require Import Cava.
Require Import AltCava.
Require Import Nand2.
Require Import AltNand.
Require Import OneBitAdder.
Require Import AltOneBitAdder.
From Coq Require Import Extraction.

Extraction Language Haskell.

Recursive Extraction Library Cava.
Recursive Extraction Library AltCava.
Extraction Library Nand2.
Extraction Library AltNand.
Extraction Library OneBitAdder.
Extraction Library AltOneBitAdder.
