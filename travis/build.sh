#!/bin/bash -x

N_JOBS=2

OS=$TRAVIS_OS_NAME

case $OS in
linux)
    # Execute docker image on Linux
    # Stop previous session
    docker rm -f prophesy &>/dev/null
    # Run container
    set -e
    docker run -d -it --name prophesy --privileged movesrwth/$DOCKER
    # Copy local content into container
    docker exec prophesy mkdir /opt/prophesy
    docker cp . prophesy:/opt/prophesy
    # Install virtualenv
    docker exec prophesy apt-get update
    docker exec prophesy apt-get install -qq -y python python3 virtualenv
    set +e

    # Execute main process
    docker exec prophesy bash -c "
        export N_JOBS=$N_JOBS;
        export OS=$OS;
        export PYTHON=$PYTHON;
        export CONFIG=$CONFIG;
        export TASK=$TASK;
        cd /opt/prophesy;
        travis/build-helper.sh"
    exit $?
    ;;

osx)
    echo "MacOS currently unsupported"
    exit 1
    ;;

*)
    # Other OS
    echo "Unsupported OS: $OS"
    exit 1
esac
