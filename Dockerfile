# Dockerfile for Prophesy
#########################
# The Docker image can be built by executing:
# docker build -t yourusername/prophesy .
# A different stormpy base image can be set from the commandline with:
# --build-arg STORMPY_BASE=<new_base_image>

# Set stormpy base image
ARG STORMPY_BASE=movesrwth/stormpy:stable
FROM $STORMPY_BASE
MAINTAINER Matthias Volk <m.volk@tue.nl>

# Install packages
RUN apt-get update -qq
RUN apt-get install -y --no-install-recommends \
    z3

# Virtual environment is already used from parent stormpy image
#ENV VIRTUAL_ENV=/opt/venv
#ENV PATH="$VIRTUAL_ENV/bin:$PATH"

# Install missing Python package
RUN pip install wheel


# Build Prophesy
################
RUN mkdir /opt/prophesy
WORKDIR /opt/prophesy

# Copy the content of the current local Prophesy repository into the Docker image
COPY . .

# Build Prophesy
RUN python setup.py develop --search-path /opt

# Uncomment to build optional dependencies
#RUN pip install -e '.[pdf]'"
