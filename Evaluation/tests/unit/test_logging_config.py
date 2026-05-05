"""Tests for centralized logging_config module."""

import logging
import os
from unittest import mock

import pytest

import src.logging_config as logging_config


@pytest.fixture(autouse=True)
def _reset_logging_config():
    """Reset module state and root logger between tests."""
    logging_config._configured = False
    root = logging.getLogger()
    old_level = root.level
    old_handlers = root.handlers[:]
    yield
    logging_config._configured = False
    root.setLevel(old_level)
    root.handlers = old_handlers


def test_get_logger_returns_logger():
    logger = logging_config.get_logger("test.module")
    assert isinstance(logger, logging.Logger)
    assert logger.name == "test.module"


def test_get_logger_default_level_info():
    """Root logger defaults to INFO when MT_LOG_LEVEL unset."""
    env = {k: v for k, v in os.environ.items() if k != "MT_LOG_LEVEL"}
    with mock.patch.dict(os.environ, env, clear=True):
        logging_config._configured = False
        logging_config._configure_root()
        assert logging.getLogger().level == logging.INFO


def test_get_logger_env_override_debug():
    """MT_LOG_LEVEL=DEBUG sets root logger to DEBUG."""
    with mock.patch.dict(os.environ, {"MT_LOG_LEVEL": "DEBUG"}):
        logging_config._configured = False
        logging_config._configure_root()
        assert logging.getLogger().level == logging.DEBUG


def test_get_logger_env_override_warning():
    """MT_LOG_LEVEL=WARNING sets root logger to WARNING."""
    with mock.patch.dict(os.environ, {"MT_LOG_LEVEL": "WARNING"}):
        logging_config._configured = False
        logging_config._configure_root()
        assert logging.getLogger().level == logging.WARNING


def test_get_logger_env_override_case_insensitive():
    """MT_LOG_LEVEL=debug (lowercase) works."""
    with mock.patch.dict(os.environ, {"MT_LOG_LEVEL": "debug"}):
        logging_config._configured = False
        logging_config._configure_root()
        assert logging.getLogger().level == logging.DEBUG


def test_get_logger_invalid_level_falls_back_to_info():
    """Invalid MT_LOG_LEVEL falls back to INFO."""
    with mock.patch.dict(os.environ, {"MT_LOG_LEVEL": "BOGUS"}):
        logging_config._configured = False
        logging_config._configure_root()
        assert logging.getLogger().level == logging.INFO


def test_configure_root_idempotent():
    """Calling _configure_root twice doesn't error or change level."""
    with mock.patch.dict(os.environ, {"MT_LOG_LEVEL": "WARNING"}):
        logging_config._configured = False
        logging_config._configure_root()
    assert logging.getLogger().level == logging.WARNING
    # Second call with different env should be no-op (_configured=True)
    with mock.patch.dict(os.environ, {"MT_LOG_LEVEL": "DEBUG"}):
        logging_config._configure_root()
    assert logging.getLogger().level == logging.WARNING


def test_log_format_constant():
    """LOG_FORMAT matches expected pattern."""
    assert "%(asctime)s" in logging_config.LOG_FORMAT
    assert "%(levelname)s" in logging_config.LOG_FORMAT
    assert "%(name)s" in logging_config.LOG_FORMAT
    assert "%(message)s" in logging_config.LOG_FORMAT
