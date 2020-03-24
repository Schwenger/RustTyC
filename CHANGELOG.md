# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.3.0] - Unreleased
### Added
- Enforce convenience features such as documentation for public functionality and the existence of debug formats for all public data structures.
- Start a changelog documenting all relevant changes throughout versions.
- Mechanism for managing keys representing variables (`rusttyc::TcVar`) inside RustTyC rather than requiring the user to do so.
- Variadic keys and TypeVariants
- 

### Fixed
- Some outdated documentation.

### Removed
- Leftover `dgb!`s.
- Ena types from public API.
- `get_type` removed because it cannot be used during the type check procedure as intended.
- Snapshotting mechanism
- Type Table Construction
- Reification

### Rename
- `TypeChecker::new_key(&mut self) -> TypeCheckKey` has been renamed to `TypeChecker::new_term_key(&mut self) -> TypeCheckKey` to distinguish it from the newly added `TypeChecker::new_var_key(&mut self, var: Var) -> TypeCheckKey`.
- `rusttyc::AbstractType` -> `rusttyc::Abstract`
- `rusttyc::TypeCheckKey` -> `rusttyc::TcKey`
- `rusttyc::TypeConstraint` -> `rusttyc::Constraint`

