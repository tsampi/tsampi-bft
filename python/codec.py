"""Canonical JSON encoding for the current BFT model."""
import dataclasses
from typing import Any

from consensus import Block, Evidence, RecordedExclusion, State, Vote


NAMES = {'inner_id': 'innerId', 'prev_vote': 'prevVote', 'prev_self': 'prevSelf',
         'sig_hash': 'sigHash', 'proposer_vote': 'proposerVote',
         'recorded_height': 'recordedHeight', 'duty_floor': 'dutyFloor'}
SHAPES = {
    State: {'chain': int, 'members': ('list', ('pair', int)), 'numerator': int,
            'denominator': int},
    Evidence: {'offender': int, 'votes': ('list', int), 'causes': ('list', 'Evidence'),
               'duty_floor': int},
    RecordedExclusion: {'proof': Evidence, 'recorded_height': int},
    Vote: {**{name: int for name in ('id', 'inner_id', 'signer', 'chain', 'height',
                                    'proposer', 'target', 'stake', 'race', 'sig_hash')},
           'prev_vote': ('option', int), 'prev_self': ('option', int),
           'exclusions': ('list', Evidence)},
    Block: {'id': int, 'parent': ('option', int), 'height': int, 'proposer': int,
            'proposer_vote': ('option', Vote), 'endorsements': ('list', Vote),
            'state': State, 'exclusions': ('list', RecordedExclusion),
            'settled': ('option', int)},
}


def wire(value) -> Any:
    if dataclasses.is_dataclass(value):
        return {NAMES.get(field.name, field.name): wire(getattr(value, field.name))
                for field in dataclasses.fields(value)}
    if isinstance(value, (set, frozenset)):
        return sorted(value)
    if isinstance(value, (tuple, list)):
        return [wire(item) for item in value]
    return value


def _keys(value, expected):
    if type(value) is not dict or set(value) != set(expected):
        raise ValueError(f'expected exactly keys {sorted(expected)}')


def decode(value, shape) -> Any:
    if shape == 'Evidence':
        shape = Evidence
    if shape is int:
        if type(value) is not int or value < 0:
            raise ValueError('expected nonnegative integer (not boolean)')
        return value
    if isinstance(shape, tuple):
        kind, child = shape
        if kind == 'option':
            return None if value is None else decode(value, child)
        if type(value) is not list or (kind == 'pair' and len(value) != 2):
            raise ValueError('expected array' if kind == 'list' else 'expected pair')
        return tuple(decode(item, child) for item in value)
    fields = SHAPES[shape]
    _keys(value, [NAMES.get(name, name) for name in fields])
    return shape(**{name: decode(value[NAMES.get(name, name)], field_shape)
                    for name, field_shape in fields.items()})
