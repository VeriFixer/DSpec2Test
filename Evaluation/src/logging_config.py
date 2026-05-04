"""Centralized logging configuration for Mutation Testing Evaluation pipeline.

Environment Variables:
    MT_LOG_LEVEL: Override default log level (default: INFO).
                  Accepts: DEBUG, INFO, WARNING, ERROR, CRITICAL.
"""

import logging
import os
import sys

LOG_FORMAT = "[%(asctime)s] %(levelname)s %(name)s: %(message)s"
DEFAULT_LEVEL = "INFO"

_configured = False


def _configure_root() -> None:
    """Configure root logger once with standard format and env-driven level."""
    global _configured
    if _configured:
        return

    level_name = os.environ.get("MT_LOG_LEVEL", DEFAULT_LEVEL).upper()
    level = getattr(logging, level_name, None)
    if not isinstance(level, int):
        level = logging.INFO

    root = logging.getLogger()
    root.setLevel(level)

    # Add handler only if root has none (avoid duplicates)
    if not root.handlers:
        handler = logging.StreamHandler(sys.stderr)
        handler.setFormatter(logging.Formatter(LOG_FORMAT))
        root.addHandler(handler)

    _configured = True


def get_logger(name: str) -> logging.Logger:
    """Return a configured logger for *name*.

    First call triggers root logger setup. Subsequent calls just return
    a child logger.
    """
    _configure_root()
    return logging.getLogger(name)
