# syntax=docker/dockerfile:1.7
# ─────────────────────────────────────────────────────────────────────────────
# DSpec2Test — Artifact Reviewer Image
#
# Builds the full DSpec2Test tool (Dafny fork with Spec mode) and the
# mutation testing evaluation pipeline in a single self-contained image.
#
# Build:
#   DOCKER_BUILDKIT=1 docker build -t dspec2test .
#
# Run interactive:
#   docker run --rm -it dspec2test
# ─────────────────────────────────────────────────────────────────────────────
FROM mcr.microsoft.com/dotnet/sdk:8.0-jammy

SHELL ["/bin/bash", "-o", "pipefail", "-c"]

ENV DEBIAN_FRONTEND=noninteractive \
    PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    PYTHONPATH=/app/Evaluation/src

WORKDIR /app

ARG Z3_VERSION=4.12.1

# ─── System packages ───────────────────────────────────────────────────────────
RUN --mount=type=cache,target=/var/cache/apt \
    --mount=type=cache,target=/var/lib/apt/lists \
    apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates curl wget sudo make build-essential unzip zip \
      python3 python3-pip python3-venv libicu-dev tzdata \
      git openssh-client openjdk-17-jdk-headless dos2unix \
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
COPY Evaluation/requirements.txt /tmp/requirements.txt
RUN python3 -m venv /opt/venv && \
    /opt/venv/bin/pip install --upgrade pip --no-cache-dir && \
    /opt/venv/bin/pip install -r /tmp/requirements.txt --no-cache-dir && \
    /opt/venv/bin/pip install pytest --no-cache-dir && \
    rm /tmp/requirements.txt
ENV PATH="/opt/venv/bin:${PATH}"

# ─── Z3 (build from source for .NET bindings) ─────────────────────────────────
RUN git clone --depth 1 --branch "z3-${Z3_VERSION}" \
      https://github.com/Z3Prover/z3.git /tmp/z3 && \
    cd /tmp/z3 && \
    python3 scripts/mk_make.py --dotnet --prefix=/usr/local && \
    cd build && \
    make -j"$(nproc)" && \
    make install && \
    chmod 755 /usr/local/bin/z3 && \
    ldconfig && \
    rm -rf /tmp/z3
ENV LD_LIBRARY_PATH="/usr/local/lib:${LD_LIBRARY_PATH}"

# ─── Build DSpec2Test (Dafny fork with Spec mode) ─────────────────────────────
COPY Source/ /app/Source/
COPY Makefile /app/Makefile
COPY dotnet-tools.json /app/.config/dotnet-tools.json

RUN find Source -name "gradlew" -exec dos2unix {} + && \
    find Source -name "gradlew" -exec chmod +x {} +

RUN --mount=type=cache,target=/root/.nuget/packages \
    dotnet build Source/Dafny.sln -c Release && \
    ln -sf /app/Binaries/net8.0/Dafny /app/Binaries/Dafny && \
    ln -sf /app/Binaries/net8.0/Dafny /usr/local/bin/dafny
ENV PATH="/app/Binaries/net8.0:${PATH}"

# ─── Build MutDafny (submodule for mutation testing) ──────────────────────────
COPY Evaluation/external/mutation/mutdafny/ /app/Evaluation/external/mutation/mutdafny/
RUN --mount=type=cache,target=/root/.nuget/packages \
    cd /app/Evaluation/external/mutation/mutdafny && \
    make -C dafny exe -j"$(nproc)" && \
    mkdir -p dafny/Binaries/z3/bin && \
    ln -s /usr/local/bin/z3 dafny/Binaries/z3/bin/z3-4.12.1 && \
    chmod 755 dafny/Binaries/z3/bin/z3-4.12.1 && \
    dotnet build mutdafny/mutdafny.csproj -c Release && \
    chmod -R a+rwX /app/Evaluation/external/mutation/mutdafny

# ─── Copy evaluation pipeline ─────────────────────────────────────────────────
COPY Evaluation/src/ /app/Evaluation/src/
COPY Evaluation/dataset/ /app/Evaluation/dataset/
COPY Evaluation/results/ /app/Evaluation/results/

# ─── Marker file for config.find_repo_root() ──────────────────────────────────
RUN touch /app/Evaluation/.repo_mutation_testing_marker

# ─── Demo examples ─────────────────────────────────────────────────────────────
COPY Example/ /app/Example/

# ─── Default shell ─────────────────────────────────────────────────────────────
CMD ["bash"]
