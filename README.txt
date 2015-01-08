Interval Arithmetic Library
===========================

This library is usable and tested, however it only works on integers (`int`) and only a few operations are implemented.

See the github issues to see the work remaining and feel free to send your PR.

Quick example:

```
// Two similars ways for creating intervals.
let a = (2, 10).to_interval();
let b = Interval::new(12, 15);

// The join operation might return more results than an union would.
// (However the union operation is not possible with interval, see SetInterval for this).
let c = a.join(b);
assert!(c == (2, 15).to_interval());

// Intersection is also implemented.
let d = a.intersect(b);
assert!(d == Interval::empty());

// and so on with difference, subset tests,...
```