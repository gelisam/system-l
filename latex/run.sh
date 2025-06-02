#!/bin/bash
set -e

clear

# List of all LaTeX files
FILES=("syntax" "rules" "example-swap" "example-swap-simplified" "example-curry")

# Function to convert a single file
convert_file() {
    local file=$1
    echo "Processing $file.tex..."
    pdflatex -halt-on-error "$file.tex"
    magick -density 150 "$file.pdf" -quality 90 "$file.png"
    echo "Created $file.png"
}

# If argument provided, convert only that file
if [ $# -eq 1 ]; then
    if [ -f "$1.tex" ]; then
        convert_file "$1"
    else
        echo "Error: $1.tex not found"
        exit 1
    fi
else
    # Convert all files
    for file in "${FILES[@]}"; do
        convert_file "$file"
    done
fi

echo "success."
