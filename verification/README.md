# Metadata validation

`formalization-v0.4.schema.json` is an unmodified copy of the official
[formalization.yaml v0.4 schema](https://github.com/mathlib-initiative/formalization.yaml/blob/99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema/v0.4.schema.json),
pinned at commit `99c678e569c7c4c0772db297c5ddd5e4c9b6322e`.
Its upstream Apache-2.0 license is reproduced in
`formalization-schema-LICENSE`; the rest of this project remains MIT licensed.

Install `verification/requirements.txt` and run `python3 scripts/validate_metadata.py`
from the repository root. The check rejects missing, malformed, and
schema-invalid metadata. An optional file path permits checking a metadata
draft against the same pinned schema. The Linux workflow runs this check
before installing Lean.

Schema validation is a metadata check. Palomar's current intake checks,
mathematical assessment, and exact-commit proof verification are separate.
