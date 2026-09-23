"""Prime-field arithmetic for GF(97) and strict value validation.

All arithmetic in this package is exact integer arithmetic modulo
``PRIME``.  No floating-point results are ever produced.
"""

import math

from .errors import ValidationError

#: The field modulus.  All circuit values live in {0, ..., PRIME - 1}.
PRIME = 97


def validate_field_value(value, *, where):
    """Validate and canonicalise one field element.

    Accepts:
      * ``int`` in canonical range ``[0, PRIME)``;
      * ``float`` that is finite and integral (e.g. ``3.0``) -- converted
        to ``int`` and then range-checked.

    Rejects (raises :class:`ValidationError`):
      * ``bool`` (even though ``bool`` is an ``int`` subclass);
      * NaN and +/-Infinity;
      * non-integral floats;
      * any other type;
      * integers outside ``[0, PRIME)`` -- out-of-range values are an
        error, they are NOT silently reduced modulo PRIME.

    ``where`` is a short locator string included in the error message.
    """
    if isinstance(value, bool):
        raise ValidationError(
            f"{where}: bool is not accepted as a field element; "
            f"use int 0 or 1"
        )
    if isinstance(value, int):
        v = value
    elif isinstance(value, float):
        if math.isnan(value) or math.isinf(value):
            raise ValidationError(
                f"{where}: NaN/Infinity are not valid field elements"
            )
        if not value.is_integer():
            raise ValidationError(
                f"{where}: non-integral float {value!r} is not a field element"
            )
        v = int(value)
    else:
        raise ValidationError(
            f"{where}: expected an int field element, "
            f"got {type(value).__name__}"
        )
    if not 0 <= v < PRIME:
        raise ValidationError(
            f"{where}: value {v} is outside the canonical range "
            f"[0, {PRIME}); reduce modulo {PRIME} explicitly if intended"
        )
    return v


def addmod(a, b):
    """(a + b) mod PRIME for already-canonical operands."""
    return (a + b) % PRIME


def mulmod(a, b):
    """(a * b) mod PRIME for already-canonical operands."""
    return (a * b) % PRIME
