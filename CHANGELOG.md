# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.3.0] - 17.07.2020

### Complete Revision of RustTyC

Forget everything that was there before.

## [0.3.1] - 20.07.2020

### Remove

* Requirement of implementing a VariantTag type.  Now uses immediate con- and destruction of types.

### Add

* Shortcuts to declare meet operations as symmetric.

### Rename

* Improved some name when generating constraints with keys.

## [0.3.2] - 24.08.2020

### Fix

* Index out of bound error resulting from incorrect determination of length in types with non-zero.

### Add

* Readme
* Constraint declaring an exact type bound for a key.
* Two `TcErr`s for handling exact type bound errors.

### Rename

* Rename TypeBound -> Bound because what else would it be?

## [0.4.0] - unpublished

### Fix

* Bug when filling vector with default elements.
* Handle child keys correctly.
* Add assertions that a key cannot be equated with itself.
* Report error when exact type bound is violated.
* Cycles in Constraint Graph lead to a unified eq class.
* Fix: Check for equality of bounds before reporting a conflict in exact bounds.
* No longer discard reification errors.
* Move TcKey management into ConstraintGraph, ditch VertexRef.

### Remove

* Exact type bounds.
* Bounding TcKeys by concrete types.

### 

* Add more convenient option to create a type checker without variables. 

### Change

* Revised abstract types entirely.