#!/usr/bin/env python3
"""Validate repository metadata against the pinned official v0.4 schema."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

import jsonschema
import yaml

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = ROOT / "verification/formalization-v0.4.schema.json"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("metadata", nargs="?", type=Path,
                        default=ROOT / "formalization.yaml")
    args = parser.parse_args()
    try:
        metadata = yaml.safe_load(args.metadata.read_text(encoding="utf-8"))
        schema = json.loads(SCHEMA.read_text(encoding="utf-8"))
        jsonschema.Draft7Validator.check_schema(schema)
        errors = list(jsonschema.Draft7Validator(schema).iter_errors(metadata))
    except (OSError, UnicodeError, ValueError, yaml.YAMLError,
            jsonschema.SchemaError) as error:
        raise SystemExit(f"Metadata validation failed: {error}") from error
    if errors:
        for error in errors:
            location = ".".join(str(part) for part in error.absolute_path) or "<root>"
            print(f"{location}: {error.message}", file=sys.stderr)
        raise SystemExit("Metadata validation failed")
    print(f"Metadata validation passed: {args.metadata.name} (official v0.4 schema)")


if __name__ == "__main__":
    main()
