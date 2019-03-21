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
  # Create virtual environment
  virtualenv --python=$PYTHON prophesy-env
  source prophesy-env/bin/activate
  # Print version
  python --version

  # Build pycarl
  travis_fold start build_pycarl
  git clone https://github.com/moves-rwth/pycarl.git
  cd pycarl
  case "$CONFIG" in
  Debug*)
    python setup.py build_ext --debug -j 1 develop
    ;;
  *)
    python setup.py build_ext -j 1 develop
    ;;
  esac
  travis_fold end build_pycarl
  cd ..

  # Build stormpy
  travis_fold start build_stormpy
  git clone https://github.com/moves-rwth/stormpy.git
  cd stormpy
  case "$CONFIG" in
  Debug*)
    python setup.py build_ext --storm-dir /opt/storm/build/ --debug -j 1 develop
    ;;
  *)
    python setup.py build_ext --storm-dir /opt/storm/build/ -j 1 develop
    ;;
  esac
  travis_fold end build_stormpy
  cd ..

  # Build prophesy
  travis_fold start build_prophesy
  python setup.py build --search-path=/opt/ develop
  travis_fold end build_prophesy

  # Perform task
  case $TASK in
  Test)
    # Install pytest
    pip install pytest
    # Run tests
    set +e
    python -m pytest tests
    python -m pytest scripts/tests
    ;;

  Documentation)
    # Generate documentation
    pip install sphinx sphinx_bootstrap_theme
    cd doc
    make html
    touch build/html/.nojekyll
    rm -r build/html/_sources
    ;;

  *)
    echo "Unrecognized value of TASK: $TASK"
    exit 1
  esac
}

run
