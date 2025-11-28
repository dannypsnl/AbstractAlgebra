"""
Generate Agda module files with default content.

Usage:
    python generate_module.py <module_name> [--title TITLE] [--taxon TAXON]

Example:
    python generate_module.py Group.IsoCayley
    python generate_module.py Ring.Def --title "環 Ring" --taxon Definition
"""

import argparse
import os
import sys
from pathlib import Path


def parse_module_name(module_name: str) -> tuple[str | None, str]:
    """
    Parse module name into directory and file parts.

    Examples:
        'Group.IsoCayley' -> ('Group', 'IsoCayley')
        'ring-0000' -> (None, 'ring-0000')

    Returns:
        (directory, filename) tuple where directory is None for single-part names
    """
    parts = module_name.split('.')
    if len(parts) < 2:
        # Single part name like 'ring-0000'
        return None, module_name

    directory = parts[0]
    filename = '.'.join(parts[1:])
    return directory, filename


def create_scrbl_content(module_name: str, title: str = None, taxon: str = None) -> str:
    """
    Generate content for .scrbl file.

    Args:
        module_name: Full module name like 'Group.IsoCayley'
        title: Optional title, defaults to module name
        taxon: Optional taxon, if not provided, no @taxon line is added
    """
    if title is None:
        title = module_name

    lines = [f"@title{{{title}}}"]

    if taxon:
        lines.append(f"@taxon{{{taxon}}}")

    lines.append("")
    lines.append(f"@disable-prefix{{@include{{../html/{module_name}.html}}}}")
    lines.append("")

    return '\n'.join(lines)


def create_lagda_content(module_name: str) -> str:
    """
    Generate content for .lagda.md file.

    Args:
        module_name: Full module name like 'Group.IsoCayley'
    """
    return f"""```agda
module {module_name} where

open import MLTT.Spartan renaming (_⁻¹ to sym; _∙_ to _then_)
open import UF.Base
open import UF.Sets
open import UF.Sets-Properties
```
"""


def create_files(module_name: str, title: str = None, taxon: str = None, force: bool = False):
    """
    Create both .scrbl and .lagda.md files for the given module.

    Args:
        module_name: Full module name like 'Group.IsoCayley' or 'ring-0000'
        title: Optional title for scrbl file
        taxon: Optional taxon for scrbl file
        force: If True, overwrite existing files
    """
    directory, filename = parse_module_name(module_name)

    # Paths
    scrbl_path = Path("content/track") / f"{module_name}.scrbl"
    if directory is None:
        # Single-part name, put directly in src/
        lagda_path = Path("src") / f"{filename}.lagda.md"
    else:
        lagda_path = Path("src") / directory / f"{filename}.lagda.md"

    # Create directories if they don't exist
    scrbl_path.parent.mkdir(parents=True, exist_ok=True)
    lagda_path.parent.mkdir(parents=True, exist_ok=True)

    # Check if files already exist
    files_to_create = []
    existing_files = []

    for path in [scrbl_path, lagda_path]:
        if path.exists() and not force:
            existing_files.append(str(path))
        else:
            files_to_create.append(path)

    if existing_files and not force:
        print("Error: The following files already exist:", file=sys.stderr)
        for f in existing_files:
            print(f"  - {f}", file=sys.stderr)
        print("\nUse --force to overwrite existing files.", file=sys.stderr)
        sys.exit(1)

    # Create .scrbl file
    scrbl_content = create_scrbl_content(module_name, title, taxon)
    scrbl_path.write_text(scrbl_content)
    print(f"Created: {scrbl_path}")

    # Create .lagda.md file
    lagda_content = create_lagda_content(module_name)
    lagda_path.write_text(lagda_content)
    print(f"Created: {lagda_path}")


def main():
    parser = argparse.ArgumentParser(
        description="Generate Agda module files with default content.",
        epilog="Example: python generate_module.py Group.IsoCayley --title 'Cayley Isomorphism'"
    )

    parser.add_argument(
        "module_name",
        help="Module name (e.g., Group.IsoCayley, Ring.Def)"
    )

    parser.add_argument(
        "--title",
        help="Title for the scrbl file (default: module name)"
    )

    parser.add_argument(
        "--taxon",
        help="Taxon for the scrbl file (e.g., Definition, Proposition)"
    )

    parser.add_argument(
        "--force",
        action="store_true",
        help="Overwrite existing files"
    )

    args = parser.parse_args()

    try:
        create_files(args.module_name, args.title, args.taxon, args.force)
    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Unexpected error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
