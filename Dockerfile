FROM debian:trixie-slim

ENV DEBIAN_FRONTEND=noninteractive \
    ELAN_HOME=/opt/elan \
    PATH=/opt/elan/bin:$PATH \
    BUN=/usr/local/bin/bun \
    BEND_COMPILER=/opt/bend/bend2/main.ts

RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential ca-certificates coq curl git make python3 unzip xz-utils \
    texlive-fonts-recommended texlive-latex-base texlive-latex-extra texlive-science \
    && rm -rf /var/lib/apt/lists/*

COPY lean/lean-toolchain /tmp/lean-toolchain
COPY bend/lean-toolchain bend/TOOLCHAIN.toml /tmp/bend/
RUN set -eu; \
    lean_toolchain="$(tr -d '\r\n' < /tmp/lean-toolchain)"; \
    bend_lean_toolchain="$(tr -d '\r\n' < /tmp/bend/lean-toolchain)"; \
    curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh; \
    sh /tmp/elan-init.sh -y --no-modify-path --default-toolchain none; \
    elan toolchain install "$lean_toolchain"; \
    elan toolchain install "$bend_lean_toolchain"; \
    elan default "$lean_toolchain"; \
    rm /tmp/lean-toolchain /tmp/elan-init.sh /tmp/bend/lean-toolchain

RUN set -eu; \
    python3 -c 'import shlex,tomllib; pin=tomllib.load(open("/tmp/bend/TOOLCHAIN.toml","rb")); keys=("repository","commit","entrypoint","base","bun_version","bun_linux_x64_baseline_sha256","bun_linux_aarch64_sha256","bun_linux_x64_baseline_binary_sha256","bun_linux_aarch64_binary_sha256"); print("\n".join("bend_"+key+"="+shlex.quote(pin[key]) for key in keys))' > /tmp/bend.env; \
    . /tmp/bend.env; \
    git init /opt/bend; \
    git -C /opt/bend remote add origin "$bend_repository"; \
    git -C /opt/bend -c http.version=HTTP/1.1 fetch --depth=1 origin "$bend_commit"; \
    git -C /opt/bend checkout --detach FETCH_HEAD; \
    test "$(git -C /opt/bend rev-parse HEAD)" = "$bend_commit"; \
    test -f "/opt/bend/$bend_entrypoint"; \
    test -f "/opt/bend/$bend_base"; \
    case "$(uname -m)" in \
      x86_64) bun_asset=bun-linux-x64-baseline; bun_archive_sha="$bend_bun_linux_x64_baseline_sha256"; bun_binary_sha="$bend_bun_linux_x64_baseline_binary_sha256" ;; \
      aarch64) bun_asset=bun-linux-aarch64; bun_archive_sha="$bend_bun_linux_aarch64_sha256"; bun_binary_sha="$bend_bun_linux_aarch64_binary_sha256" ;; \
      *) exit 1 ;; \
    esac; \
    curl -fsSL "https://github.com/oven-sh/bun/releases/download/bun-v$bend_bun_version/$bun_asset.zip" -o /tmp/bun.zip; \
    printf '%s  /tmp/bun.zip\n' "$bun_archive_sha" | sha256sum -c -; \
    unzip -q /tmp/bun.zip -d /tmp/bun; \
    install -m 0755 "/tmp/bun/$bun_asset/bun" /usr/local/bin/bun; \
    printf '%s  /usr/local/bin/bun\n' "$bun_binary_sha" | sha256sum -c -; \
    test "$(bun --version)" = "$bend_bun_version"; \
    rm -rf /tmp/bend /tmp/bend.env /tmp/bun /tmp/bun.zip

WORKDIR /src
COPY . .
RUN make verify
CMD ["make", "help"]
