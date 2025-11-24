import os
import re
from pathlib import Path

def process_file(filepath):
    """Process a single HTML file to convert links to absolute paths without .html"""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()

    original = content

    # Replace href="filename.html#anchor" with href="/filename#anchor"
    content = re.sub(r'href="([^"/:]+)\.html(#[^"]*)"', r'href="/\1\2"', content)
    # Replace href="filename.html" with href="/filename"
    content = re.sub(r'href="([^"/:]+)\.html"', r'href="/\1"', content)

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

    html_files = list(html_dir.glob('*.html'))
    count = 0

    for filepath in html_files:
        if process_file(filepath):
            count += 1
            print(f"Modified: {filepath}")

    print(f"\nTotal files modified: {count}")

if __name__ == '__main__':
    main()
