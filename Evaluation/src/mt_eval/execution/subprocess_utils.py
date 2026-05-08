"""Subprocess utilities — run with proper process-group cleanup on timeout."""

import os
import signal
import subprocess
from dataclasses import dataclass


@dataclass
class SubprocessResult:
    """Mirrors subprocess.CompletedProcess essentials."""
    returncode: int
    stdout: str
    stderr: str


def run_with_cleanup(
    cmd: list[str],
    timeout: int,
    cwd: str | None = None,
) -> SubprocessResult:
    """Run a subprocess, killing the entire process group on timeout.

    Uses start_new_session=True so all child processes (e.g., dotnet spawned
    by Dafny) belong to a killable process group.

    Args:
        cmd: Command to execute.
        timeout: Max seconds before killing.
        cwd: Working directory for the subprocess.

    Returns:
        SubprocessResult on normal completion.

    Raises:
        subprocess.TimeoutExpired: If timeout exceeded (after cleanup).
        Exception: On other subprocess errors.
    """
    proc = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
        cwd=cwd,
    )
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
        return SubprocessResult(
            returncode=proc.returncode,
            stdout=stdout or "",
            stderr=stderr or "",
        )
    except subprocess.TimeoutExpired:
        # Kill entire process group
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        except (ProcessLookupError, OSError):
            proc.kill()
        proc.wait()
        raise
