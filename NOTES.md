Reduction Rules
===============

# Head

### Pure Nil

- Can't reduce
- Singleton

```haskell
More (t,Nothing)
  Nil
```

# Tail

### Remove Nils

```haskell
More (t,mx)
  xs
---------------
More (t,mx)
  removeNils xs
```

### Long Nil

```haskell
More (t,Nothing)
  More (t',Nothing)
    More (t'',Nothing)
      ...
        Nil
----------------------
Nil
```

# Arbitrary

## Singleton Chains

### Long Just

> Singleton Just

```haskell
More (t,Just x)
  Nil
---------------
Rest [t] x
```

> More General

```haskell
More (t,Nothing)
  More (t',Nothing)
    More (t'',Nothing)
      ...
        More (t_n, Just x)
--------------------------
Rest (t..t_n) x
```
