/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Lake
import Lake.Config.Meta

public section

open Lean

namespace Lake.Serialized

open System

public protected structure ConfigDecl where
  pkg : Name
  name : Name
  kind : Name
  -- config : ConfigType kind pkg name
  -- wf_data : ¬ kind.isAnonymous → CustomData pkg name = DataType kind ∧ DataType kind = OpaqueConfigTarget kind
  deriving TypeName, ToJson, FromJson

def _root_.Lake.ConfigDecl.toSerializedConfigDecl (c : ConfigDecl) :
    Serialized.ConfigDecl := { c with }

public protected structure PConfigDecl (p : Name) extends Serialized.ConfigDecl where
  pkg_eq : toConfigDecl.pkg = p := by rfl

public protected structure NConfigDecl (p n : Name) extends Serialized.PConfigDecl p where
  name_eq : toConfigDecl.name = n := by rfl

public protected structure KConfigDecl (k : Name) extends Serialized.ConfigDecl where
  kind_eq : toConfigDecl.kind = k := by rfl

def _root_.Lake.PConfigDecl.toSerializedPConfigDecl (c : PConfigDecl p) :
    Serialized.PConfigDecl p :=
  { c with }

def _root_.Lake.NConfigDecl.toSerializedNConfigDecl (c : NConfigDecl p n) :
    Serialized.NConfigDecl p n :=
  { c with }

def _root_.Lake.KConfigDecl.toSerializedKConfigDecl (c : KConfigDecl p) :
    Serialized.KConfigDecl p :=
  { c with }

instance : ToJson (Serialized.PConfigDecl p) where
  toJson p := toJson p.toConfigDecl

instance : FromJson (Serialized.PConfigDecl p) where
  fromJson? j := fromJson? (α := Serialized.ConfigDecl) j |>.bind fun c =>
    if pkg_eq : c.pkg = p then .ok { c with pkg_eq } else
      .error s!"Expected PConfigDecl to have package name {p}, instead got:\n\
        {toJson c}"

instance : ToJson (Serialized.NConfigDecl p n) where
  toJson p := toJson p.toPConfigDecl

instance : FromJson (Serialized.NConfigDecl p n) where
  fromJson? j := fromJson? (α := Serialized.PConfigDecl p) j |>.bind fun c =>
    if name_eq : c.name = n then .ok { c with name_eq } else
      .error s!"Expected NConfigDecl to have name {n}, instead got:\n\
        {toJson c}"

instance : ToJson (Serialized.KConfigDecl k) where
  toJson p := toJson p.toConfigDecl

instance : FromJson (Serialized.KConfigDecl k) where
  fromJson? j := fromJson? (α := Serialized.ConfigDecl) j |>.bind fun c =>
    if kind_eq : c.kind = k then .ok { c with kind_eq } else
      .error s!"Expected KConfigDecl to have kind {k}, instead got:\n\
        {toJson c}"

-- #synth ToJson BuildKey

deriving instance ToJson, FromJson for BuildKey
deriving instance ToJson, FromJson for PartialBuildKey
deriving instance ToJson, FromJson for WorkspaceConfig
deriving instance ToJson, FromJson for BuildType
deriving instance ToJson, FromJson for LeanOption
deriving instance ToJson, FromJson for DependencySrc
deriving instance ToJson, FromJson for Dependency

-- Needed since `deriving` demands `[ToJson α]`
instance : ToJson (Target α) where
  toJson t := .obj (({} : Std.TreeMap.Raw String Json) |>.insert "key" (toJson t.key))

instance : FromJson (Target α) where
  fromJson? t := t.getObjVal? "key" |>.bind fromJson? |>.map ({ key := · })

instance : ToJson (TargetArray α) where
  toJson a := Array.toJson a

instance : FromJson (TargetArray α) where
  fromJson? a := Array.fromJson? a

deriving instance ToJson, FromJson for Backend

set_option linter.unusedVariables false in
public configuration SerializedPackageConfig (p : Name) (n : Name) extends
    WorkspaceConfig, LeanConfig where
  /-- **For internal use.** Whether this package is Lean itself. -/
  bootstrap : Bool := false

  /--
  **This field is deprecated.**

  The path of a package's manifest file, which stores the exact versions
  of its resolved dependencies.

  Defaults to `defaultManifestFile` (i.e., `lake-manifest.json`).
  -/
  manifestFile : Option FilePath := none

  /-- An `Array` of target names to build whenever the package is used. -/
  extraDepTargets : Array Name := #[]

  /--
  Whether to compile each of the package's module into a native shared library
  that is loaded whenever the module is imported. This speeds up evaluation of
  metaprograms and enables the interpreter to run functions marked `@[extern]`.

  Defaults to `false`.
  -/
  precompileModules : Bool := false

  /--
  Additional arguments to pass to the Lean language server
  (i.e., `lean --server`) launched by `lake serve`, both for this package and
  also for any packages browsed from this one in the same session.
  -/
  moreGlobalServerArgs, moreServerArgs : Array String := #[]

  /--
  The directory containing the package's Lean source files.
  Defaults to the package's directory.

  (This will be passed to `lean` as the `-R` option.)
  -/
  srcDir : FilePath := "."

  /--
  The directory to which Lake should output the package's build results.
  Defaults to `defaultBuildDir` (i.e., `.lake/build`).
  -/
  buildDir : FilePath := defaultBuildDir

  /--
  The build subdirectory to which Lake should output the package's
  binary Lean libraries (e.g., `.olean`, `.ilean` files).
  Defaults to  `defaultLeanLibDir` (i.e., `lib`).
  -/
  leanLibDir : FilePath := defaultLeanLibDir

  /--
  The build subdirectory to which Lake should output the package's
  native libraries (e.g., `.a`, `.so`, `.dll` files).
  Defaults to `defaultNativeLibDir` (i.e., `lib`).
  -/
  nativeLibDir : FilePath := defaultNativeLibDir

  /--
  The build subdirectory to which Lake should output the package's binary executable.
  Defaults to `defaultBinDir` (i.e., `bin`).
  -/
  binDir : FilePath := defaultBinDir

  /--
  The build subdirectory to which Lake should output
  the package's intermediary results (e.g., `.c` and `.o` files).
  Defaults to `defaultIrDir` (i.e., `ir`).
  -/
  irDir : FilePath := defaultIrDir

  /--
  The URL of the GitHub repository to upload and download releases of this package.
  If `none` (the default), for downloads, Lake uses the URL the package was download
  from (if it is a dependency) and for uploads, uses `gh`'s default.
  -/
  releaseRepo, releaseRepo? : Option String := none

  /--
  A custom name for the build archive for the GitHub cloud release.
  If `none` (the default), Lake defaults to `{(pkg-)name}-{System.Platform.target}.tar.gz`.
  -/
  buildArchive, buildArchive? : Option String := none

  /--
  Whether to prefer downloading a prebuilt release (from GitHub) rather than
  building this package from the source when this package is used as a dependency.
  -/
  preferReleaseBuild : Bool := false

  /--
  The name of the script, executable, or library by `lake test` when
  this package is the workspace root. To point to a definition in another
  package, use the syntax `<pkg>/<def>`.

  A script driver will be run by `lake test` with the arguments
  configured in `testDriverArgs`  followed by any specified on the CLI
  (e.g., via  `lake lint -- <args>...`). An executable driver will be built
  and then run like a script. A library will just be built.
  -/
  testDriver, testRunner : String := ""

  /--
  Arguments to pass to the package's test driver.
  These arguments will come before those passed on the command line via
  `lake test -- <args>...`.
  -/
  testDriverArgs : Array String := #[]

  /--
  The name of the script or executable used by `lake lint` when this package
  is the workspace root. To point to a definition in another package, use the
  syntax `<pkg>/<def>`.

  A script driver will be run by `lake lint` with the arguments
  configured in `lintDriverArgs` followed by any specified on the CLI
  (e.g., via  `lake lint -- <args>...`). An executable driver will be built
  and then run like a script.
  -/
  lintDriver : String := ""

  /--
  Arguments to pass to the package's linter.
  These arguments will come before those passed on the command line via
  `lake lint -- <args>...`.
  -/
  lintDriverArgs : Array String := #[]

  /--
  The package version. Versions have the form:

  ```
  v!"<major>.<minor>.<patch>[-<specialDescr>]"
  ```

  A version with a `-` suffix is considered a "prerelease".

  Lake suggest the following guidelines for incrementing versions:

  * **Major version increment** *(e.g., v1.3.0 → v2.0.0)*
    Indicates significant breaking changes in the package.
    Package users are not expected to update to the new version
    without manual intervention.

  * **Minor version increment** *(e.g., v1.3.0 → v1.4.0)*
    Denotes notable changes that are expected to be
    generally backwards compatible.
    Package users are expected to update to this version automatically
    and should be able to fix any breakages and/or warnings easily.

  * **Patch version increment** *(e.g., v1.3.0 → v1.3.1)*
    Reserved for bug fixes and small touchups.
    Package users are expected to update automatically and should not expect
    significant breakage, except in the edge case of users relying on the
    behavior of patched bugs.

  **Note that backwards-incompatible changes may occur at any version increment.**
  The is because the current nature of Lean (e.g., transitive imports,
  rich metaprogramming, reducibility in proofs), makes it infeasible to
  define a completely stable interface for a package.
  Instead, the different version levels indicate a change's intended significance
  and how difficult migration is expected to be.

  Versions of form the `0.x.x` are considered development versions prior to
  first official release. Like prerelease, they are not expected to closely
  follow the above guidelines.

  Packages without a defined version default to `0.0.0`.
  -/
  version : StdVer := {}

  -- /--
  -- Git tags of this package's repository that should be treated as versions.
  -- Package indices (e.g., Reservoir) can make use of this information to determine
  -- the Git revisions corresponding to released versions.

  -- Defaults to tags that are "version-like".
  -- That is, start with a `v` followed by a digit.
  -- -/
  -- versionTags : StrPat := defaultVersionTags

  /-- A short description for the package (e.g., for Reservoir). -/
  description : String := ""

  /--
  Custom keywords associated with the package.
  Reservoir can make use of a package's keywords to group related packages
  together and make it easier for users to discover them.

  Good keywords include the domain (e.g., `math`, `software-verification`,
  `devtool`), specific subtopics (e.g., `topology`,  `cryptology`), and
  significant implementation details (e.g., `dsl`, `ffi`, `cli`).
  For instance, Lake's keywords could be `devtool`, `cli`, `dsl`,
  `package-manager`, and `build-system`.
  -/
  keywords : Array String := #[]

  /--
  A URL to information about the package.

  Reservoir will already include a link to the package's GitHub repository
  (if the package is sourced from there). Thus, users are advised to specify
  something else for this (if anything).
  -/
  homepage : String := ""

  /--
  The package's license (if one).
  Should be a valid [SPDX License Expression][1].

  Reservoir requires that packages uses an OSI-approved license to be
  included in its index, and currently only supports single identifier
  SPDX expressions. For, a list of OSI-approved SPDX license identifiers,
  see the [SPDX LIcense List][2].

  [1]: https://spdx.github.io/spdx-spec/v3.0/annexes/SPDX-license-expressions/
  [2]: https://spdx.org/licenses/
  -/
  license : String := ""

  /--
  Files containing licensing information for the package.

  These should be the license files that users are expected to include when
  distributing package sources, which may be more then one file for some licenses.
  For example, the Apache 2.0 license requires the reproduction of a `NOTICE`
  file along with the license (if such a file exists).

  Defaults to `#["LICENSE"]`.
  -/
  licenseFiles : Array FilePath := #["LICENSE"]

  /--
  The path to the package's README.

  A README should be a Markdown file containing an overview of the package.
  Reservoir displays the rendered HTML of this file on a package's page.
  A nonstandard location can be used to provide a different README for Reservoir
  and GitHub.

  Defaults to `README.md`.
  -/
  readmeFile : FilePath := "README.md"

  /--
  Whether Reservoir should include the package in its index.
  When set to `false`, Reservoir will not add the package to its index
  and will remove it if it was already there (when Reservoir is next updated).
  -/
  reservoir : Bool := true

  /--
  Whether to enables Lake's local, offline artifact cache for the package.

  Artifacts (i.e., build products) of packages will be shared across
  local copies by storing them in a cache associated with the Lean toolchain.
  This can significantly reduce initial build times and disk space usage when
  working with multiple copies of large projects or large dependencies.

  As a caveat, build targets which support the artifact cache will not be stored
  in their usual location within the build directory. Thus, projects with custom build
  scripts that rely on specific location of artifacts may wish to disable this feature.

  If `none` (the default), this will fallback to (in order):
  * The `LAKE_ARTIFACT_CACHE` environment variable (if set).
  * The workspace root's `enableArtifactCache` configuration (if set and this package is a dependency).
  * **Lake's default**: The package can use artifacts from the cache, but cannot write to it.
  -/
  enableArtifactCache?, enableArtifactCache : Option Bool := none

  /--
  Whether, when the local artifact cache is enabled, Lake should copy all cached
  artifacts into the build directory. This ensures the build results are available
  to external consumers who expect them in the build directory.

  Defaults to `false`.
  -/
  restoreAllArtifacts : Bool := false

  /--
  Whether native libraries (of this package) should be prefixed with `lib` on Windows.

  Unlike Unix, Windows does not require native libraries to start with `lib` and,
  by convention, they usually do not. However, for consistent naming across all platforms,
  users may wish to enable this.

  Defaults to `false`.
  -/
  libPrefixOnWindows : Bool := false

  /--
  Whether downstream packages can `import all` modules of this package.

  If enabled, downstream users will be able to access the `private` internals of modules,
  including definition bodies not marked as `@[expose]`.
  This may also, in the future, prevent compiler optimization which rely on `private`
  definitions being inaccessible outside their own package.

  Defaults to `false`.
  -/
  allowImportAll : Bool := false

deriving Inhabited, ToJson, FromJson

def _root_.Lake.PackageConfig.toSerializedPackageConfig (cfg : PackageConfig p n) :
    SerializedPackageConfig p n :=
  { cfg with }

/--
A package `Script` is a named `ScriptFn` definition with a some optional documentation.

It can be run by `lake run <name> [-- <args>]`.
-/
public protected structure Script where
  /-- The full name of the `Script` (e.g., `pkg/script`). -/
  name : String
  -- fn : ScriptFn
  doc? : Option String
  deriving Inhabited, ToJson, FromJson

def _root_.Lake.Script.toSerializedScript (s : Script) : Serialized.Script :=
  { s with }

instance : ToJson (DNameMap (Serialized.NConfigDecl keyName)) where
  toJson map := toJson <| map.toArray.map fun ⟨a, b⟩ => (a, b.toPConfigDecl)

instance : FromJson (DNameMap (Serialized.NConfigDecl keyName)) where
  fromJson? map := do
    let e ← fromJson? (α := Array (Name × Serialized.PConfigDecl keyName)) map
    let mut map : DNameMap (Serialized.NConfigDecl keyName) := {}
    for (name, decl) in e do
      if name_eq : decl.name = name then
        map := map.insert name { decl with name_eq }
      else
        throw s!"Expected NConfigDecl to have name equal to {name}, instead got\n{toJson e}"
    return map

/-- A Lake package -- its location plus its configuration. -/
public protected structure Package where
  /-- The index of the package in the workspace. Used to disambiguate packages with the same name. -/
  wsIdx : Nat
  /-- The assigned name of the package. -/
  baseName : Name
  /-- The package identifier used in target keys and configuration types. -/
  keyName : Name := baseName.num wsIdx
  /-- The name specified by the package. -/
  origName : Name
  /-- The absolute path to the package's directory. -/
  dir : FilePath
  /-- The path to the package's directory relative to the workspace. -/
  relDir : FilePath
  /-- The package's user-defined configuration. -/
  config : SerializedPackageConfig keyName origName
  /-- The absolute path to the package's configuration file. -/
  configFile : FilePath
  /-- The path to the package's configuration file (relative to `dir`). -/
  relConfigFile : FilePath
  /-- The path to the package's JSON manifest of remote dependencies (relative to `dir`). -/
  relManifestFile : FilePath := config.manifestFile.getD defaultManifestFile |>.normalize
  /-- The package's scope (e.g., in Reservoir). -/
  scope : String
  /-- The URL to this package's Git remote. -/
  remoteUrl : String
  /-- Dependency configurations for the package. -/
  depConfigs : Array Dependency := #[]
  /-- Target configurations in the order declared by the package. -/
  targetDecls : Array (Serialized.PConfigDecl keyName) := #[]
  /-- Name-declaration map of target configurations in the package. -/
  targetDeclMap : DNameMap (Serialized.NConfigDecl keyName) :=
    targetDecls.foldl (fun m d => m.insert d.name (.mk d rfl)) {}
  /--
  The names of the package's targets to build by default
  (i.e., on a bare `lake build` of the package).
  -/
  defaultTargets : Array Name := #[]
  /-- Scripts for the package. -/
  scripts : NameMap Serialized.Script := {}
  /--
  The names of the package's scripts run by default
  (i.e., on a bare `lake run` of the package).
  -/
  defaultScripts : Array Serialized.Script := #[]
  -- /-- Post-`lake update` hooks for the package. -/
  -- postUpdateHooks : Array (OpaquePostUpdateHook keyName) := #[]
  /-- The package's `buildArchive`/`buildArchive?` configuration. -/
  buildArchive : String :=
    if let some n := config.buildArchive then n else defaultBuildArchive baseName
  /-- The driver used for `lake test` when this package is the workspace root. -/
  testDriver : String := config.testDriver
  /-- The driver used for `lake lint` when this package is the workspace root. -/
  lintDriver : String := config.lintDriver
  -- /--
  -- Input-to-output(s) map for hashes of package artifacts.
  -- If `none`, the artifact cache is disabled for the package.
  -- -/
  -- inputsRef? : Option CacheRef := none
  -- /--
  -- Input-to-output(s) map for hashes of package artifacts.
  -- If `none`, the artifact cache is disabled for the package.
  -- -/
  -- outputsRef? : Option CacheRef := none
deriving ToJson, FromJson

def _root_.Lake.Package.toSerializedPackage (pkg : Package) : Serialized.Package :=
  { pkg with
    config := pkg.config.toSerializedPackageConfig
    targetDecls := pkg.targetDecls.map (·.toSerializedPConfigDecl)
    targetDeclMap := pkg.targetDeclMap.map fun _ decl => decl.toSerializedNConfigDecl
    scripts := pkg.scripts.map fun _ s => s.toSerializedScript
    defaultScripts := pkg.defaultScripts.map (·.toSerializedScript)
  }

deriving instance FromJson for Dynlib

deriving instance ToJson, FromJson for Cache, ElanInstall, LeanInstall, LakeInstall
deriving instance ToJson, FromJson for Lake.Env

/-- A facet's declarative configuration. -/
public protected structure FacetConfig (name : Name) : Type where
  /-- The facet kind (i.e., the kind of targets that support this facet). -/
  kind : Name
  -- /-- The facet's fetch function. -/
  -- fetchFn : DataType kind → FetchM (Job (FacetOut name))
  -- /-- The optional data kind of the facet's output. -/
  -- [outKind : OptDataKind (FacetOut name)]
  /-- Is this facet compatible with the `lake build` CLI? -/
  buildable : Bool := true
  -- /-- Format this facet's output (e.g., for `lake query`). -/
  -- format : OutFormat → FacetOut name → String
  /-- Whether the fetch of this facet should be cached in the Lake build store. -/
  memoize : Bool := true
  deriving Inhabited, ToJson, FromJson

def _root_.Lake.FacetConfig.toSerializedFacetConfig (cfg : FacetConfig name) :
    Serialized.FacetConfig name := { cfg with }

/-- A package with a name known at type-level. -/
public structure Serialized.NPackage (n : Name) extends Serialized.Package where
  keyName_eq : toPackage.keyName = n

def _root_.Lake.NPackage.toSerializedNPackage (pkg : NPackage name) :
    Serialized.NPackage name := { pkg with toPackage := pkg.toSerializedPackage }

instance : ToJson (Serialized.NPackage p) where
  toJson p := toJson p.toPackage

instance : FromJson (Serialized.NPackage p) where
  fromJson? j := fromJson? (α := Serialized.Package) j |>.bind fun c =>
    if keyName_eq : c.keyName = p then .ok { c with keyName_eq } else
      .error s!"Expected PConfigDecl to have package name {p}, instead got:\n\
        {toJson c}"

instance : ToJson (DNameMap Serialized.NPackage) where
  toJson map := toJson <| map.toArray.map fun ⟨a, b⟩ => (a, b.toPackage)

instance : FromJson (DNameMap Serialized.NPackage) where
  fromJson? map := do
    let e ← fromJson? (α := Array (Name × Serialized.Package)) map
    let mut map : DNameMap Serialized.NPackage := {}
    for (name, decl) in e do
      if keyName_eq : decl.keyName = name then
        map := map.insert name { decl with keyName_eq }
      else
        throw s!"Expected NPackage to have keyName equal to {name}, instead got\n{toJson e}"
    return map

instance : ToJson (DNameMap Serialized.FacetConfig) where
  toJson map := .arr <| map.toArray.map fun ⟨name, cfg⟩ => .mkObj [
    ("key", toJson name),
    ("val", toJson cfg)
  ]

instance : FromJson (DNameMap Serialized.FacetConfig) where
  fromJson? map := do
    let arr ← map.getArr?
    let mut map : DNameMap Serialized.FacetConfig := {}
    for a in arr do
      let key ← a.getObjValAs? Name "key"
      let val ← a.getObjValAs? (Serialized.FacetConfig key) "val"
      map := map.insert key val
    return map

/-- A Lake workspace -- the top-level package directory. -/
public protected structure Workspace : Type where
  /-- The root package of the workspace. -/
  root : Serialized.Package
  /-- The detected {lean}`Lake.Env` of the workspace. -/
  lakeEnv : Lake.Env
  /-- The Lake cache. -/
  lakeCache : Cache
    -- := if root.bootstrap then lakeEnv.lakeSystemCache?.getD ⟨root.lakeDir / "cache"⟩
    -- else lakeEnv.lakeCache?.getD ⟨root.lakeDir / "cache"⟩
  /--
  The CLI arguments Lake was run with.
  Used by {lit}`lake update` to perform a restart of Lake on a toolchain update.
  A value of {lean}`none` means that Lake is not restartable via the CLI.
  -/
  lakeArgs? : Option (Array String) := none
  /--
  The packages within the workspace
  (in {lit}`require` declaration order with the root coming first).
  -/
  packages : Array Serialized.Package := {}
  /-- Name-package map of packages within the workspace. -/
  packageMap : DNameMap Serialized.NPackage := {}
  /-- Configuration map of facets defined in the workspace. -/
  facetConfigs : DNameMap Serialized.FacetConfig := {}
deriving ToJson, FromJson

def _root_.Lake.Workspace.toSerializedWorkspace (ws : Workspace) : Serialized.Workspace :=
  { ws with
    root := ws.root.toSerializedPackage
    packages := ws.packages.map (·.toSerializedPackage)
    packageMap := ws.packageMap.map fun _ pkg => pkg.toSerializedNPackage
    facetConfigs := ws.facetConfigs.map fun _ cfg => cfg.toSerializedFacetConfig
  }
