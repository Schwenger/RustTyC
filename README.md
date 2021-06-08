# RustTyC

[![Crate](https://img.shields.io/crates/v/rusttyc.svg)](https://crates.io/crates/rusttyc)
[![API](https://docs.rs/rusttyc/badge.svg)](https://docs.rs/rusttyc)
[![License](https://img.shields.io/crates/l/rusttyc)](https://crates.io/crates/rusttyc)


<img src="http://mschwenger.de/assets/img/thumbnails/rusttyc.svg" alt="RustTyC Logo" title="RustTyC Logo" style="width: 10em; border: none; float: right;"/>

RustTyC is a simple interface for translating type rules into rust and performs the type checking procedure to generate a type table.

## TL;DR

- Add dependency from [crates.io](https://crates.io/crates/rusttyc "crates.io").
- Check out the [documentation](https://schwenger.github.io/RustTyC/ "documentation").
- Basic introduction to type lattices and inference rules on my [blog](https://mschwenger.de/projects/rusttyc.html "blog").

# What is RustTyC?

RustTyC provides an interface that allows for an intuitive translation of inference rules based on a Hindney-Milner-like bounded type meet-semilattice into rust code.  

# Usage

The first and most obvious step is to add the dependency to your `Cargo.toml`:

```
rusttyc = "0.4.*"
```

Next, let's talk data structures. I assume you already have some code data structure representing programs you want to type-check. We'll call this the AST. Then, you need some representation of types, which we'll call `AbsTy`. Most likely, this is an enum listing all possible types a value can have, including unresolved types (`Top/Unconstrained/Infer`), abstract types (`Numeric`) and recursive type (`Option(Box<AbsTy>)` or `Either(Box<AbsTy>, Box<AbsTy>)`).

To obtain a lattice structure, implement the `rusttyc::Variant` type. This requires you to implement three functions and provide an associated error type (`Variant::Err`). Before getting to the meet of the implementation (do you see what I did there?), let's cover the simple functions: `Variant::top()`, which provides the top element of the type lattice, and `Variant::arity(&self) -> Arity`, which provides the arity of a specific type. The arity can be either `Arity::Variable` or `Arity::Fixed(usize)`. Nothing too exciting here. Lastly, there is the `Variant::meet(Partial<Self>, Partial<Self>) -> Result<Partial<Self>, Self::Err>` function. If you forget about the Partial thingy for a second, this is exactly what we would expect: it takes two abstract types and provides a new one according to the rules for type lattices. If the two types are incompatible, it returns an error with some debug information. Note that type checker will enrich the error with some more context information to make it easily traceable, hence producing a `TcErr`. If you are curious, have a glance at its documentation. So, what's the deal with the `Partial`? A `Partial` is the combination of a `Variant` and the least number of children the respective type has. So, for example, a numeric type typically does not have a child. Thus, when wrapped in a `Partial` its `Partial::least_arity` will always be 0. A tuple-type, however, is a different story entirely. Suppose a variable represents a nonuple (9-tuple), but the type inference only infered that there will be a child at places 0, 3 and 4. In this case, its `Partial::least_arity` will be 5 (recall: index 4 occupied indicates at least 5 elements). Similarly, if the type is the top variant, it might resolve to a tuple or an option, hence it arity can only be a lower bound.

What's left to do now is to start collecting constraints. In your code, create a new type checker with `rusttyc::TypeChecker::new()` and traverse your AST. For each node in the AST create a `rusttyc::TcKey` and impose a set of constraints on it. The key represents either a node of the AST (whatever this may be) or a variable. The special point of variables is that they might occur several times in the AST and refer to the same object. There are several ways to handle this challenge, the by far easiest is to let the type checker take care of it. For this, call the `TypeChecker::get_var_key(&mut self, var: Var) -> TcKey` function. Calling this function multiple times with the same variable will return the same key; for your convenience.

Assume the AST is the tree representation of `c := a + 3`. You'll want to traverse the tree by recursively calling a `tc_ast` function. Assume `tc` is the type checker and the function returns a `Result<TcKey, TcErr<AbsTy>>` where the key is the key containing the type of the node. We'll discuss the nodes bottom to top.  The first node is the variable `a`. There's not much to do here, just retrieve a key for `a` and return it: `Ok(tc.get_var_key(var))`. Next is the integer literal 3. Assume such a literal should bind the value to the type `AbsTy::Unsigned`. Thus, use:

```rust
let key = tc.new_term_key();  // Generate a fresh key.
tc.impose(key.more_conc_than_explicit(AbsTy::Unsigned))?;  // Set an explicit abstract type as bound for `key`.
Ok(key)
```

Now the interesting part: performing the addition. The idea is to check both sub-terms recursively, meet their types, and return the result.

```rust
let left = tc_expr(&mut tc, lhs);
let right = tc_expr(&mut tc, rhs);
let key = tc.new_term_key();
tc.impose(key.is_meet_of(left, right))?;
Ok(key)
```

Well, that was simpler than expected, eh?

Let's wrap up by assigning the value. For this, we recursively check the expression, retrieve the key for `c` and equate it with the result of the expression.

```rust
let res = tc_expr(rhs);
let key = tc.get_var_key(lhs);
tc.impose(lhs.is_sym_meet_of(key))?;
Ok(key)
```

And that's it!
Retrieve the result of the whole procedure by generating a type table.
```rust
let type_table = tc.type_check()?;
```

### (A-)Symmetric Relations

One thing you need to keep in mind is that type relations are like friendships: some are symmetric, some are not. And all is well if everyone is aware of that. So RustTyc offers to impose both kinds of relations. A symmetric relation between two keys `k`, and `k'` entails that a refinement of one also refines the other. Suppose `k` is in an asymmetric relation with `k'`, e.g. `k` is more concrete than `k'`. In this case, refining the type of `k'` entails a refinement of `k`, but not vice versa. A regular meet (`TcKey::is_meet_of(...)`) is inherently asymmetric, the symmetric counterpart is `TcKey::is_sym_meet_of(...)`.
