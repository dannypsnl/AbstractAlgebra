import os
import re
from pathlib import Path

def load_known_addrs():
    """Load known addresses from content/track/*.scrbl files"""
    known_addrs = set()
    track_dir = Path('content/track')

    if not track_dir.exists():
        return known_addrs

    for scrbl_file in track_dir.glob('*.scrbl'):
        with open(scrbl_file, 'r', encoding='utf-8') as f:
            content = f.read()
            # Extract module name from @disable-prefix{@include{../html/XXX.html}}
            matches = re.findall(r'@include\{\.\.\/html\/([^}]+)\.html\}', content)
            known_addrs.update(matches)

    return known_addrs

def process_file(filepath, known_addrs):
    """Process a single HTML file to convert links based on known addresses"""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()

    original = content

    def replace_link(match):
        addr = match.group(1)
        anchor = match.group(2) if match.lastindex >= 2 and match.group(2) else ''

        if addr in known_addrs:
            # Known address: use local link
            return f'href="/{addr}{anchor}"'
        else:
            # Unknown address: use TypeTopology link with target="_blank"
            return f'href="https://martinescardo.github.io/TypeTopology/{addr}.html{anchor}" target="_blank"'

    # Replace href="filename.html" or href="filename.html#anchor"
    # Match relative links with .html extension
    content = re.sub(r'href="([A-Za-z0-9._-]+)\.html(#[^"]*)?(")',
                     lambda m: replace_link(m) + '"',
                     content)

    # Add target="_blank" to external TypeTopology links that don't have it yet
    content = re.sub(r'href="(https://martinescardo\.github\.io/TypeTopology/[^"]+)"(?!\s+target="_blank")',
                     r'href="\1" target="_blank"',
                     content)

    if content != original:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(content)
        return True

    return False

def main():
    """Process all HTML files in the html directory"""
    html_dir = Path('html')

    if not html_dir.exists():
        print(f"Error: Directory '{html_dir}' does not exist")
        return

    # Load known addresses from track files
    known_addrs = load_known_addrs()
    print(f"Loaded {len(known_addrs)} known addresses from content/track/")

    html_files = list(html_dir.glob('*.html'))
    count = 0

    for filepath in html_files:
        if process_file(filepath, known_addrs):
            count += 1
            print(f"Modified: {filepath}")

    print(f"\nTotal files modified: {count}")

if __name__ == '__main__':
    main()
