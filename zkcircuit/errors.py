"""Error taxonomy for the zkcircuit package.

Every error raised by this package derives from ``CircuitError`` so callers
can catch one base type, while each failure mode stays individually
catchable and carries a message that locates the offending input.
"""


class CircuitError(Exception):
    """Base class for all errors raised by zkcircuit."""


class ValidationError(CircuitError, ValueError):
    """A public-API argument violated the documented contract.

    Raised for: non-Node arguments, NaN/Infinity numbers, bool passed where
    a field integer is required, out-of-range field values, bad node
    structure, wrong witness shape, etc.  Nothing is silently corrected.
    """


class NodeLimitError(CircuitError):
    """The DAG exceeds the documented maximum of unique nodes."""


class DuplicateInputNameError(CircuitError):
    """Two distinct ``input`` nodes share the same name."""


class WitnessInputError(CircuitError):
    """Base class for problems with the input-value mapping."""


class MissingInputError(WitnessInputError):
    """A required input variable has no supplied value."""


class UnknownInputError(WitnessInputError):
    """A supplied key does not correspond to any variable of the circuit."""


class IntermediateOverrideError(WitnessInputError):
    """A supplied key names an intermediate/aux slot, which user input
    is not allowed to override."""
