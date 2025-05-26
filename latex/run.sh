#!/bin/bash
set -e

clear
pdflatex -halt-on-error system-l.tex
echo "success."
