# Security policy

## Supported versions

Fixes go to `main` and ship in a new tag. Only the latest tag is supported.

## Reporting a vulnerability

Please do not open a public issue. Report privately through [GitHub private vulnerability reporting](https://github.com/whoiam1101/fulcrum/security/advisories/new) or by email to samvelsafaryan1313@gmail.com.

A determinism bug counts as a security issue: if two platforms produce different bits for the same input, a lockstep game built on fulcrum can desync or be exploited. Please include the inputs, the targets and both outputs.
