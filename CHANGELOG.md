# CHANGELOG

## [0.0.2]

### Changed

- Refactor `Passdata` constructors to create a new instance with a `Schema` or
  an unchecked `Vec<u8>` and `Schema`.
- Use a single `Vec<u8>` to store data instead of multiple `Vec` or `BTreeMap`
  instances. Allow easier serialization/deserialization.
- Use byte slices as a primitive value type instead of strings
  Refactor `Constant` to use byte slice instead of a `Cow<'_, str>`.
- Make `AnyBool`, `AnyNum`, and `AnyStr` public
- Remove `ArrayLength` generic arguments in functions

### Added

- Add `Schema` for describing stored data
- Add `Passdata::into_inner` which returns the underlying byte vector which
  stores the data.
- Add `contains_edb` and `query_only_one_edb` methods to `Passdata`
- Add `edb_iter` to iterate through declared facts. A `FactTerms` is the `Item`
  returned which allows the constants to be filled in an existing buffer or a
  new `Vec`.
- Add `predicates_iter` to iterate through predicates
- Implement `QueryResult` for non-tuple types which implement `QueryValue`
- Add `AnyConstant` as a possible `QueryValue`
- Implement `IntoArray` for `&[u8]`
- Derive `PartialEq` to error types

## [0.0.1]

### Added

- Initial implementation

[Unreleased]: https://github.com/bluk/passdata/compare/v0.1.0...HEAD
[0.2.0]: https://github.com/bluk/passdata/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/bluk/passdata/releases/tag/v0.1.0
[0.0.2]: https://github.com/bluk/passdata/compare/v0.0.1...v0.0.2
[0.0.1]: https://github.com/bluk/passdata/releases/tag/v0.0.1