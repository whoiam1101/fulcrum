# fulcrum

[![ci](https://github.com/whoiam1101/fulcrum/actions/workflows/ci.yml/badge.svg)](https://github.com/whoiam1101/fulcrum/actions/workflows/ci.yml)
[![codeql](https://github.com/whoiam1101/fulcrum/actions/workflows/codeql.yml/badge.svg)](https://github.com/whoiam1101/fulcrum/actions/workflows/codeql.yml)
[![license](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)
[![msrv](https://img.shields.io/badge/MSRV-1.60-orange.svg)](Cargo.toml)

fulcrum is a deterministic fixed-point math library for Rust. Every operation, including sqrt, sin, cos and atan2, gives bit-identical results on x86-64 and ARM64, with no floating point used internally. Overflow is explicit and never panics. It includes 2D/3D vectors and stable serialization for snapshots, replays and checksums. It is no_std and suited to lockstep networking, replays and any simulation that must agree across machines.

> **Status:** early development. The architecture is in [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md); the API is not implemented yet.

## Citation

If you use fulcrum in research or a published project, please cite it. GitHub shows a ready-made citation under **Cite this repository** (from [`CITATION.cff`](CITATION.cff)), or use:

```bibtex
@software{safaryan_fulcrum_2026,
  author  = {Safaryan, Samvel},
  title   = {fulcrum: deterministic fixed-point math for Rust},
  year    = {2026},
  url     = {https://github.com/whoiam1101/fulcrum},
  license = {Apache-2.0}
}
```

## License

Copyright 2026 Samvel Safaryan.

Licensed under the [Apache License, Version 2.0](LICENSE). Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in this project shall be licensed as above, without any additional terms or conditions.
