# Passdata

`Passdata` is authentication and authorization data expressed in a logic
programming language. Data should fit within the limits of a HTTP cookie or
header. The language is limited in order to guarantee execution characteristics
during execution.

Applications and services which accept `Passdata` are intended to be usable
without the need to contact a centralized service for every operation.

The library is experimental and is not intended for production usage.

## Alternatives

There are many alternatives which are considered production ready. It is
strongly recommended to look into these alternatives.

* HTTP sessions
* [JSON Web Tokens (JWT)](https://datatracker.ietf.org/doc/html/rfc7519)
* [Pasteo](https://paseto.io)
* [Macroons](https://www.ndss-symposium.org/ndss2014/programme/macaroons-cookies-contextual-caveats-decentralized-authorization-cloud/)
* [Biscuit](https://www.biscuitsec.org)

### Differences from Alternatives

Compared to traditional HTTP sessions, `Passdata` does not require a server side
persistence data store. More computation is done in the application code to
process `Passdata`, but the tradeoff may be desirable in situations where compute
is cheap but the cost in persisting and retrieving from storage is high.

JSON Web Tokens and Pasteo are primarily used with a limited set of predefined
data fields. `Passdata` allows arbitrary data.

`Passdata` is not focused on token attenutation unlike Macaroons and Biscuits.

`Passdata` is most similar to Biscuits which has its own logic programming
language. However, `Passdata` has a more limited logic programming language in
order to provide better guarantees on possible resource usage.

## License

Licensed under either of [Apache License, Version 2.0][LICENSE_APACHE] or [MIT
License][LICENSE_MIT] at your option.

### Contributions

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

[LICENSE_APACHE]: LICENSE-APACHE
[LICENSE_MIT]: LICENSE-MIT
