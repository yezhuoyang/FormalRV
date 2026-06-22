"""FTQ-VM: a Fault-Tolerant Quantum Virtual Machine.

A discrete-event simulator / checker for finite-service resource contracts
in fault-tolerant quantum computation.  It does NOT simulate quantum
amplitudes; it executes a declared schedule of logical / QEC / system calls
against a backend description of finite resources, checks the schedule for
resource-contract violations, and produces traces, statistics and a
machine-checkable certificate.
"""

__version__ = "0.1.0"
