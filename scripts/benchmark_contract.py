#!/usr/bin/env python3
"""Strict scalar and JSON parsing shared by the two benchmark tracks."""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import subprocess
import sys
from typing import Any

MAX_CENTIBITS = 100_000
MAX_FRACTION_COMPONENT = 2**63 - 1
MIN_UNSAFE_INDEX = 1
PROFILE_PARAMETERS = {
    "half": {"domainSize": 2**22, "baseDimension": 2**21, "totalDimension": 2**27, "repetitions": 256},
    "quarter": {"domainSize": 2**21, "baseDimension": 2**19, "totalDimension": 2**25, "repetitions": 128},
}

def split_track(track: str) -> tuple[str, str]:
    if track not in {"half-lower", "half-upper", "quarter-lower", "quarter-upper"}:
        raise ValueError(f"unknown binary track: {track}")
    return tuple(track.split("-"))

MAX_SCALAR_BYTES = 128
MAX_RESULT_BYTES = 4 * 1024 * 1024
FULL_COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")


def parse_nat(
    raw: str, *, label: str, minimum: int = 0, maximum: int
) -> int:
    """Parse one canonical ASCII Nat in a caller-supplied closed interval."""
    if not isinstance(raw, str) or not raw or not raw.isascii() or not raw.isdecimal():
        raise ValueError(f"{label} must be a non-negative ASCII decimal integer")
    value = int(raw, 10)
    if raw != str(value):
        raise ValueError(f"{label} must use canonical decimal notation")
    if not minimum <= value <= maximum:
        raise ValueError(f"{label} must lie between {minimum} and {maximum}")
    return value


def parse_json_nat(
    value: object, *, label: str, minimum: int = 0, maximum: int
) -> int:
    """Parse a JSON integer without coercing strings, booleans, or floats."""
    if type(value) is not int:
        raise ValueError(f"{label} must be a JSON integer")
    return parse_nat(
        str(value), label=label, minimum=minimum, maximum=maximum
    )


def parse_centibits(raw: str, *, label: str = "centibits") -> int:
    return parse_nat(raw, label=label, minimum=0, maximum=MAX_CENTIBITS)


def parse_radius(raw: str) -> tuple[int, int]:
    parts = raw.split("/")
    if len(parts) != 2:
        raise ValueError("radius must be an exact NUMERATOR/DENOMINATOR fraction")
    numerator = parse_nat(
        parts[0],
        label="radius numerator",
        minimum=1,
        maximum=MAX_FRACTION_COMPONENT,
    )
    denominator = parse_nat(
        parts[1],
        label="radius denominator",
        minimum=1,
        maximum=MAX_FRACTION_COMPONENT,
    )
    if numerator >= denominator:
        raise ValueError("radius fraction must lie strictly between zero and one")
    return numerator, denominator


def parse_unsafe_index(raw: str, *, profile: str = "half", label: str = "unsafe index") -> int:
    return parse_nat(
        raw,
        label=label,
        minimum=MIN_UNSAFE_INDEX,
        maximum=PROFILE_PARAMETERS[profile]["domainSize"] - PROFILE_PARAMETERS[profile]["baseDimension"],
    )


def read_scalar(path: str | Path) -> str:
    """Read one non-empty printable-ASCII line, with at most one final newline."""
    scalar_path = Path(path)
    data = scalar_path.read_bytes()
    if len(data) > MAX_SCALAR_BYTES:
        raise ValueError(f"{scalar_path} is too large for a scalar claim")
    if data.endswith(b"\r\n"):
        data = data[:-2]
    elif data.endswith(b"\n"):
        data = data[:-1]
    if not data or b"\r" in data or b"\n" in data:
        raise ValueError(f"{scalar_path} must contain exactly one non-empty line")
    try:
        value = data.decode("ascii")
    except UnicodeDecodeError as error:
        raise ValueError(f"{scalar_path} must contain ASCII text") from error
    # benchmark.sh transports this value through command substitution, which
    # silently drops NUL bytes. Reject every control byte before that boundary.
    if any(not 0x20 <= byte <= 0x7E for byte in data):
        raise ValueError(f"{scalar_path} must contain printable ASCII text")
    return value


def load_json_object(path: str | Path) -> dict[str, Any]:
    """Load bounded JSON while rejecting duplicate keys and non-finite numbers."""
    result_path = Path(path)
    data = result_path.read_bytes()
    if len(data) > MAX_RESULT_BYTES:
        raise ValueError(f"{result_path} is too large")

    def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate JSON key: {key}")
            result[key] = value
        return result

    def reject_constant(value: str) -> None:
        raise ValueError(f"non-finite JSON number is not allowed: {value}")

    try:
        value = json.loads(
            data,
            object_pairs_hook=unique_object,
            parse_constant=reject_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValueError(f"invalid JSON in {result_path}: {error}") from error
    if not isinstance(value, dict):
        raise ValueError(f"{result_path} must contain a JSON object")
    return value


def parse_commit(value: object, *, label: str) -> str:
    if not isinstance(value, str) or FULL_COMMIT_RE.fullmatch(value) is None:
        raise ValueError(f"{label} must be a lowercase 40-digit hexadecimal commit")
    return value


def arklib_revision(manifest_path: str | Path = "lake-manifest.json") -> str:
    manifest = load_json_object(manifest_path)
    packages = manifest.get("packages")
    if not isinstance(packages, list):
        raise ValueError("lake-manifest.json has no package list")
    matches = [
        package
        for package in packages
        if isinstance(package, dict) and package.get("name") == "Arklib"
    ]
    if len(matches) != 1:
        raise ValueError("lake-manifest.json must contain exactly one Arklib package")
    return parse_commit(matches[0].get("rev"), label="Arklib revision")


def submission_revision() -> str:
    if github_sha := os.environ.get("GITHUB_SHA"):
        return parse_commit(github_sha, label="GITHUB_SHA")
    revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], text=True, encoding="ascii"
    ).strip()
    return parse_commit(revision, label="submission revision")


def atomic_write_json(path: str | Path, value: object) -> None:
    output = Path(path)
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_suffix(output.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")
    os.replace(temporary, output)


def atomic_write_text(path: str | Path, value: str) -> None:
    output = Path(path)
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_suffix(output.suffix + ".tmp")
    temporary.write_text(value, encoding="utf-8")
    os.replace(temporary, output)


def main() -> None:
    if len(sys.argv) != 3 or sys.argv[1] != "read-scalar":
        raise SystemExit("usage: benchmark_contract.py read-scalar PATH")
    try:
        print(read_scalar(sys.argv[2]))
    except (OSError, ValueError) as error:
        raise SystemExit(str(error)) from error


if __name__ == "__main__":
    main()
