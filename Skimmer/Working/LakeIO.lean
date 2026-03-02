/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Lean
public import Skimmer.Refactor.Lake
public import Lake
public import Skimmer.LakeSerialized

open Lean Meta Elab Lake

public section

@[inline] def IO.Process.Output.toExcept (o : IO.Process.Output) : Except String String :=
  if o.exitCode = 0 then .ok o.stdout else .error o.stderr

@[inline] def IO.Process.Output.toExceptWithExitCode (o : IO.Process.Output) :
    Except String String :=
  if o.exitCode = 0 then .ok o.stdout else
    .error s!"Process exited with code {o.exitCode}:\n{o.stderr}"

/-- Considers success to be given by exit code 0. Returns stdout in that case, or throws. -/
@[inline] def IO.ofOutput (o : IO.Process.Output) : IO String :=
  .ofExcept <| o.toExcept

/-- Considers success to be given by exit code 0. Returns stdout in that case, or throws, displaying the exit code in the merror message as well. -/
@[inline] def IO.ofOutputWithExitCode (o : IO.Process.Output) : IO String :=
  .ofExcept <| o.toExceptWithExitCode

namespace IO.Lake

def build (target : PartialBuildKey) (input? : Option String := none) : IO Unit := do
  discard <| IO.Process.run (input? := input?) {
    cmd := "lake"
    args := #["build", target.toString]
  }

def _root_.Lake.PartialBuildKey.customTarget (target : Name) (pkg : Name := .anonymous) :
    PartialBuildKey :=
  BuildKey.customTarget pkg target

def _root_.Lake.PartialBuildKey.module (mod : Name) (pkg : Name := .anonymous) :
    PartialBuildKey :=
  if pkg.isAnonymous then BuildKey.module mod else BuildKey.packageModule pkg mod

def _root_.Lake.PartialBuildKey.moduleFacet (mod facet : Name) (pkg : Name := .anonymous) :
    PartialBuildKey :=
  BuildKey.packageModule pkg mod |>.facet facet

-- TODO: would be nice to have static checking here, but that doesn't seem very practical outside of the lakefile.
def query (target : PartialBuildKey) (α : Type) [FromJson α] (input? : Option String := none) :
    IO α := do
  let output ← IO.Process.output (input? := input?) {
    cmd := "lake"
    args := #["query", "--json", target.toString]
  }
  .ofExcept (← .ofOutput output).toJson

def runScript (script : String) (args : Array String := #[]) : IO String := do
  let output ← IO.Process.output {
    cmd := "lake"
    args := #["script", "run", script] ++ args
  }
  .ofOutput output

def checkTarget (key : Array PartialBuildKey) : IO Unit := do
  discard <| runScript "checkTarget" (key.map (·.toString))

def getSerializedWorkspace : IO Serialized.Workspace :=
  query (.customTarget `workspace) Serialized.Workspace
