#!/usr/bin/env python3
"""Check this repository's Palomar source, configuration, and metadata surface.

Requires PyYAML. This preflight complements, and does not replace, Comparator
and Palomar's verification of the exact submitted commit.
"""

import json
import os
from pathlib import Path
import re
import sys
import tomllib

import yaml


ROOT = Path(__file__).resolve().parents[1]
THEOREMS = [
    "not_RamanujanCongruence_verbose",
    "RamanujanCongruence_5_verbose",
    "RamanujanCongruence_7_verbose",
    "RamanujanCongruence_11_verbose",
]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def without_comments(text):
    """Remove leading Lean comments, including nested block comments."""
    while True:
        text = text.lstrip()
        if text.startswith("--"):
            text = text.partition("\n")[2]
        elif text.startswith("/-"):
            depth, pos = 1, 2
            while depth and pos < len(text):
                if text[pos:pos + 2] == "/-":
                    depth, pos = depth + 1, pos + 2
                elif text[pos:pos + 2] == "-/":
                    depth, pos = depth - 1, pos + 2
                else:
                    pos += 1
            require(depth == 0, "Unterminated leading Lean comment")
            text = text[pos:]
        else:
            return text


class UniqueLoader(yaml.SafeLoader):
    pass


def unique_mapping(loader, node):
    result = {}
    for key_node, value_node in node.value:
        require(key_node.value != "<<", "YAML merge keys are not permitted")
        key = loader.construct_object(key_node)
        require(key not in result, f"Duplicate YAML key: {key}")
        result[key] = loader.construct_object(value_node)
    return result


UniqueLoader.add_constructor(
    yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, unique_mapping
)


def main():
    source_count = 0
    for directory, subdirs, files in os.walk(ROOT):
        subdirs[:] = [d for d in subdirs if d not in {".git", ".lake"}]
        for name in files:
            if not name.endswith(".lean"):
                continue
            path = Path(directory) / name
            relative = path.relative_to(ROOT)
            require(not path.is_symlink(), f"Lean symlink: {relative}")
            text = path.read_text(encoding="utf-8")
            lines = text.count("\n") + bool(text and not text.endswith("\n"))
            require(lines <= 10000, f"Source exceeds 10,000 lines: {relative}")
            if name != "lakefile.lean":
                require(re.match(r"module\s", without_comments(text)),
                        f"Missing module header: {relative}")
            source_count += 1

    challenge = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    require(len(challenge.encode("utf-8")) <= 100 * 1024,
            "Challenge exceeds 100 KiB")
    require(challenge.count("\n") + bool(not challenge.endswith("\n")) <= 1000,
            "Challenge exceeds 1,000 lines")
    imports = re.findall(r"^(?:public )?import\s+(\S+)", challenge, re.M)
    require(imports and all(i.startswith("Mathlib.") for i in imports),
            "Challenge must import only Mathlib")
    require(re.findall(r"^def\s+(\w+)", challenge, re.M) == ["partition"],
            "partition must be the sole Challenge definition")
    require(re.findall(r"^theorem\s+(\w+)", challenge, re.M) == THEOREMS,
            "Unexpected Challenge theorem list")

    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    require(config == {
        "challenge_module": "Challenge", "solution_module": "Solution",
        "theorem_names": THEOREMS, "definition_names": [],
        "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
    }, "Comparator configuration differs from the intended audit surface")

    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    for package in manifest["packages"]:
        if package["type"] == "git":
            require(re.fullmatch(r"[0-9a-f]{40}", package["rev"]),
                    f"Unpinned dependency: {package['name']}")
            require(re.fullmatch(r"https://github.com/[\w.-]+/[\w.-]+", package["url"]),
                    f"Noncanonical dependency URL: {package['name']}")
        elif package["type"] == "path":
            target = (ROOT / package["dir"]).resolve()
            require(target.is_relative_to(ROOT), "Path dependency escapes checkout")
            require((target / "lake-manifest.json").is_file(),
                    "Contained dependency must commit its manifest")
            config_path = target / package["configFile"]
            require(config_path.suffix == ".toml",
                    "Check the build directory of non-TOML path dependencies manually")
            package_config = tomllib.loads(config_path.read_text(encoding="utf-8"))
            build_dir = (target / package_config.get("buildDir", ".lake/build")).resolve()
            writable = [ROOT / ".lake/build", target / ".lake/build"]
            require(any(build_dir.is_relative_to(directory) for directory in writable),
                    f"Path dependency {package['name']} builds outside Palomar's "
                    "writable .lake/build directories")
        else:
            raise ValueError(f"Unsupported dependency: {package['name']}")

    metadata = yaml.load((ROOT / "formalization.yaml").read_text(encoding="utf-8"),
                         Loader=UniqueLoader)
    require(metadata["version"] == "v0.4", "Expected formalization.yaml v0.4")
    project = metadata["project"]
    for key in ("name", "description", "authors", "responsible_maintainers"):
        require(project[key], f"Missing project.{key}")
    require(project["license"] == "Apache-2.0", "Expected Apache-2.0 metadata")
    require("Apache License" in (ROOT / "LICENSE").read_text(encoding="utf-8"),
            "Missing Apache licence text")
    require(1 <= len(metadata["classification"]["arxiv"]) <= 2,
            "Expected one or two arXiv classifications")
    require(1 <= len(metadata["classification"]["msc2020"]) <= 8,
            "Expected one to eight MSC2020 classifications")
    require(metadata["sources"] and any(s["relationship"] in {
        "formalizes", "adapts", "independently-proves"
    } for s in metadata["sources"]), "Expected source-based provenance")
    require(all(s["title"] and s["relationship"] in {
        "formalizes", "adapts", "independently-proves", "background", "other"
    } for s in metadata["sources"]), "Invalid source entry")
    require(metadata["automation"]["methods"] and metadata["review"]["status"],
            "Missing automation or review disclosure")
    require([s["lean"] for s in metadata["alignment"]["statements"]] == THEOREMS,
            "Metadata alignment must cover the four selected theorems")
    print(f"Palomar preflight passed: {source_count} Lean files, four theorems, "
          "one concrete statement definition, and source-based metadata.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError, yaml.YAMLError) as error:
        print(f"Palomar preflight failed: {error}", file=sys.stderr)
        sys.exit(1)
