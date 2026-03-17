#!/bin/bash
set -e 

echo "--- 1. Fixing Git Permissions & Ownership ---"
# Hardcoding the path ensures the script works even if the VS Code variable isn't passed
git config --global --add safe.directory /workspaces/polarized-proof-search
git config --global --add safe.directory /workspaces/polarized-proof-search/rocq-carve

echo "--- 2. Setting Fallback Git Identity ---"
if [ -z "$(git config --global user.email)" ]; then
    git config --global user.email "research-team@mcgill.ca"
    git config --global user.name "Research Team"
fi

echo "--- 3. Initializing Submodules ---"
git submodule update --init --recursive

echo "--- 4. Loading OPAM Environment ---"
eval $(opam env)

echo "--- 5. Building the Project ---"
# Generate the Coq Makefile
rocq makefile -f _CoqProject -o Makefile

# Build submodule
if [ -d "rocq-carve" ]; then
    cd rocq-carve
    if [ -f "./configure" ]; then ./configure; fi
    make -j$(nproc)
    cd ..
fi

# Build main logic
make -j$(nproc)

echo "--- SETUP COMPLETE ---"