# Security policy

## Supported versions

fulcrum is in early development; only the latest commit on `main` is supported.

## Reporting a vulnerability

Please do not open a public issue. Report privately through [GitHub private vulnerability reporting](https://github.com/whoiam1101/fulcrum/security/advisories/new) or by email to samvelsafaryan1313@gmail.com.

Determinism bugs count as security issues too: if two platforms produce different bits for the same input, a lockstep game built on fulcrum can desync or be exploited. Please include the inputs, the targets and both outputs.
