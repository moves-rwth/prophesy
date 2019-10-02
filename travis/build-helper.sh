#!/bin/bash

set -e

# Helper for travis folding
travis_fold() {
  local action=$1
  local name=$2
  echo -en "travis_fold:${action}:${name}\r"
}

# Helper for building and testing
run() {
  travis_fold start virtualenv
  if [[ "$CONFIG" != *Stormpy* ]]
  then
    # Create virtual environment
    virtualenv --python=$PYTHON venv
  fi
  # Activate virtual environment
  source venv/bin/activate
  # Print version
  python --version
  travis_fold end virtualenv

  # Build prophesy
  travis_fold start build_prophesy
  python setup.py develop --search-path=/opt/
  travis_fold end build_prophesy

  # Perform task
  if [[ "$TASK" == *Test* ]]
  then
    # Install pytest
    pip install pytest
    # Run tests
    set +e
    python -m pytest tests
    python -m pytest scripts/tests
  fi

  if [[ "$TASK" == *Documentation* ]]
  then
    # Generate documentation
    pip install sphinx sphinx_bootstrap_theme
    cd doc
    make html
    touch build/html/.nojekyll
    rm -r build/html/_sources
  fi
}

run
