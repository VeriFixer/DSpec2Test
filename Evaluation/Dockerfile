# syntax=docker/dockerfile:1.7
# ─────────────────────────────────────────────────────────────────────────────
# Mutation Testing Evaluation Pipeline
#
# Build context MUST be the repository root (parent of Evaluation/):
#   docker build -f Evaluation/Dockerfile -t mt-eval .
# ─────────────────────────────────────────────────────────────────────────────
FROM ubuntu:22.04

SHELL ["/bin/bash", "-o", "pipefail", "-c"]

ENV DEBIAN_FRONTEND=noninteractive \
    PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    PYTHONPATH=/app/src

WORKDIR /app

ARG Z3_VERSION=4.12.1

# ─── System packages ───────────────────────────────────────────────────────────
RUN --mount=type=cache,target=/var/cache/apt \
    --mount=type=cache,target=/var/lib/apt/lists \
    apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates curl wget sudo make build-essential unzip zip \
      python3 python3-pip python3-venv libicu-dev tzdata \
      git openssh-client openjdk-17-jdk \
    && rm -rf /var/lib/apt/lists/*

# ─── .NET SDK 8 ───────────────────────────────────────────────────────────────
RUN curl -fsSL https://dot.net/v1/dotnet-install.sh -o /tmp/dotnet-install.sh && \
    bash /tmp/dotnet-install.sh --channel 8.0 --install-dir /usr/share/dotnet && \
    ln -sfn /usr/share/dotnet/dotnet /usr/local/bin/dotnet && \
    rm -f /tmp/dotnet-install.sh

# ─── Java HOME ────────────────────────────────────────────────────────────────
RUN JAVA_ARCH=$(dpkg --print-architecture) && \
    ln -s "/usr/lib/jvm/java-17-openjdk-${JAVA_ARCH}" /usr/lib/jvm/default-java
ENV JAVA_HOME=/usr/lib/jvm/default-java

# ─── Python dependencies ──────────────────────────────────────────────────────
COPY Evaluation/requirements.txt /app/requirements.txt
RUN python3 -m venv /opt/venv && \
    /opt/venv/bin/pip install --upgrade pip && \
    /opt/venv/bin/pip install -r /app/requirements.txt && \
    /opt/venv/bin/pip install pytest
ENV PATH="/opt/venv/bin:${PATH}"

# ─── Z3 (build from source for .NET bindings) ─────────────────────────────────
RUN git clone --depth 1 --branch "z3-${Z3_VERSION}" \
      https://github.com/Z3Prover/z3.git /tmp/z3 && \
    cd /tmp/z3 && \
    python3 scripts/mk_make.py --dotnet && \
    cd build && \
    make -j"$(nproc)" && \
    make install && \
    chmod 755 /usr/local/bin/z3 && \
    ldconfig
ENV LD_LIBRARY_PATH="/usr/local/lib:${LD_LIBRARY_PATH}"

# ─── Build Dafny (this repo IS the fork with SpecTestGenerator) ───────────────
# Copy the full repo source needed for the build
COPY Source/ /app/dafny-repo/Source/
COPY Makefile /app/dafny-repo/Makefile
RUN --mount=type=cache,target=/root/.nuget/packages \
    cd /app/dafny-repo && \
    dotnet build Source/Dafny.sln -c Release && \
    ln -sf /app/dafny-repo/Binaries/Dafny /usr/local/bin/dafny
ENV PATH="/app/dafny-repo/Binaries:${PATH}"

# ─── Build MutDafny (submodule: custom Dafny fork + Z3 + plugin) ──────────────
COPY Evaluation/external/mutation/mutdafny/ /app/external/mutation/mutdafny/
RUN --mount=type=cache,target=/root/.nuget/packages \
    cd /app/external/mutation/mutdafny && \
    make -C dafny exe -j"$(nproc)" && \
    cd dafny/Binaries && \
    wget -q https://github.com/dafny-lang/solver-builds/releases/download/snapshot-2023-08-02/z3-4.12.1-x64-ubuntu-20.04-bin.zip && \
    unzip -q z3-4.12.1-x64-ubuntu-20.04-bin.zip && \
    mv z3-4.12.1 z3 && \
    chmod 755 z3 && \
    rm -f z3-4.12.1-x64-ubuntu-20.04-bin.zip && \
    cd /app/external/mutation/mutdafny && \
    dotnet build mutdafny/mutdafny.csproj -c Release && \
    chmod -R a+rwX /app/external/mutation/mutdafny

# ─── Copy pipeline source and dataset scripts ─────────────────────────────────
COPY Evaluation/src/ /app/src/
COPY Evaluation/dataset/ /app/dataset/

# Marker file for config.find_repo_root()
COPY Evaluation/.repo_mutation_testing_marker /app/

CMD ["bash"]
