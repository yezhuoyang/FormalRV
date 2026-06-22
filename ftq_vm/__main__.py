"""Entry point so that ``python -m ftq_vm`` works."""

from ftq_vm.backend.cli import main

if __name__ == "__main__":
    raise SystemExit(main())
