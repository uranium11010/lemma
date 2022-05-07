"""
Classes for types of abstractions
"""

import json
import numpy as np
import warnings
import argparse

from steps import *
import util

import doctest


class Abstraction:
    @staticmethod
    def new(config, steps, ex_states=None):
        if config.get("consider_pos", False):
            if config.get("tree_idx", False):
                return AxSeqTreePos(steps, ex_states)
            return AxSeqRelPos(steps, ex_states)
        return AxiomSeq(steps, ex_states)

    def has_instance(self, steps):
        """
        Checks whether abstraction has `steps` as instance
        """
        raise NotImplementedError()

    def within(self, steps):
        """
        Checks whether abstraction is present among a list of steps
        (e.g. Solution.actions tuple)
        """
        num_ax = len(self.axioms)
        return any(self.has_instance(steps[i:i+num_ax]) for i in range(len(steps)-num_ax+1))

    def __lt__(self, other):
        return False


class AxiomSeq(Abstraction):
    """
    Abstraction: sequence of axioms

    >>> AxiomSeq([Step("refl"), Step([Step("sub~comm $~3, 1~3x"), Step("comm 2, 2x")])]).axioms
    ('refl', 'sub~comm~comm')
    """

    def __init__(self, args, ex_states=None):
        """
        Builds abstraction from list of Step objects or list of axioms
        """
        if all(isinstance(step, Step) for step in args):
            self.ex_steps = args
            self.ex_states = ex_states
            self.axioms = tuple(step.name_str for step in args)
        elif all(isinstance(step_name, str) for step_name in args):
            self.axioms = tuple(args)
        self.freq = None
        self.rel_pos_freq = None
        self.rel_pos_ex_steps = None

    def has_instance(self, steps):
        """
        >>> seq = AxiomSeq([Step("refl"), Step("sub~comm $~3, 1~3x")])
        >>> seq.within((Step("refl~refl $~$, $~$"), Step("refl"), Step([Step("sub 1"), Step("comm 6, 1y")])))
        True
        """
        return all(axiom == step.name_str for axiom, step in zip(self.axioms, steps))

    def __str__(self):
        try:
            return self.name_str
        except AttributeError:
            self.name_str = '~'.join(self.axioms)
            return self.name_str

    def __repr__(self):
        return f"AxiomSeq{self.axioms}"

    def __eq__(self, other):
        return self.axioms == other.axioms

    def __hash__(self):
        return hash(self.axioms)


class AxSeqRelPos(Abstraction):
    """
    Abstraction: sequence of axioms + relative positions of application
    DOES NOT FULLY SUPPORT NESTED ABSTRACTIONS (CURRENTLY LOSES POSITION INFO)

    >>> AxSeqRelPos([Step("refl"), Step((AxStep("sub 1"), Step("comm 3, 3x"))), Step("comm 2, 2x")]).rel_pos
    (None, -1)
    """

    def __init__(self, steps, ex_states=None):
        """
        Builds abstraction from list of Step objects
        """
        self.ex_steps = steps
        self.ex_states = ex_states
        self.freq = None
        self.axioms = tuple(step.name_str for step in steps)
        self.rel_pos = tuple(int(steps[i+1].head_idx) - int(steps[i].head_idx)
                             if steps[i+1].head_idx is not None and steps[i].head_idx is not None
                             else None
                             for i in range(len(steps)-1))


    def has_instance(self, steps):
        """
        >>> seq = AxSeqRelPos([Step("eval 3, 2/2"), Step([Step("sub~comm $~3, 1~3x")])])
        >>> seq.within((Step("refl~refl $~$, $~$"), Step("eval 3, 1/5"), Step([Step("sub 1"), AxStep("comm 6, 1y")])))
        False
        >>> seq.within((Step("refl~refl $~$, $~$"), Step("eval 5, 1/5"), Step([Step("sub 1"), AxStep("comm 5, 1y")])))
        True
        """
        if not all(axiom == step.name_str for axiom, step in zip(self.axioms, steps)):
            return False
        return all(self.rel_pos[i] is None or int(steps[i+1].head_idx) - int(steps[i].head_idx) == self.rel_pos[i] for i in range(len(self.rel_pos)))

    def __str__(self):
        try:
            return f"{self.name_str} {self.pos_str}"
        except AttributeError:
            self.name_str = '~'.join(self.axioms)
            self.pos_str = '~'.join('$' if pos is None else str(pos) for pos in self.rel_pos)
            return f"{self.name_str} {self.pos_str}"

    def __repr__(self):
        return f"AxSeqRelPos({self.axioms}, {self.rel_pos})"

    def __eq__(self, other):
        return self.axioms == other.axioms and self.rel_pos == other.rel_pos

    def __hash__(self):
        return hash(self.axioms) + hash(self.rel_pos)


class AxSeqTreePos(Abstraction):
    """
    Abstraction: sequence of axioms + relative positions of application within tree
    DOES NOT SUPPORT ABSTRACTIONS OF ABSTRACTIONS (head_idx defined badly)

    >>> AxSeqTreePos([Step("refl"), Step((AxStep("sub 1"), Step("comm 0.0.1, 3x"))), Step("comm 0.1, 2x")]).rel_pos
    ((None, '0.0.1'), ('0.1', '1'))
    """

    def __init__(self, steps, ex_states=None):
        """
        Builds abstraction from list of Step objects
        step.head_idx must be a bit string
        """
        self.ex_steps = steps
        self.ex_states = ex_states
        self.freq = None
        self.axioms = tuple(step.name_str for step in steps)
        self.rel_pos = tuple(AxSeqTreePos.remove_prefix(steps[i].head_idx, steps[i+1].head_idx)
                             for i in range(len(steps)-1))

    @staticmethod
    def remove_prefix(idx1, idx2):
        """
        Given idx1 and idx2 (strings of bits), remove maximal common prefix
        """
        if idx1 is None:
            if idx2 is None:
                return None, None
            else:
                return None, idx2
        else:
            if idx2 is None:
                return idx1, None
            else:
                for i in range(min(len(idx1), len(idx2))):
                    if idx1[i] != idx2[i]:
                        break
                return idx1[i:], idx2[i:]

    def has_instance(self, steps):
        """
        >>> seq = AxSeqTreePos([Step("eval 0.1, 2/2"), Step([Step("sub~comm $~0.0, 1~3x")])])
        >>> seq.within((Step("refl~refl $~$, $~$"), Step("eval 0.0.1, 1/5"), Step([Step("sub 1"), AxStep("comm 0.1.1.1, 1y")])))
        False
        >>> seq.within((Step("refl~refl $~$, $~$"), Step("eval 0.1.1.1, 1/5"), Step([Step("sub 1"), AxStep("comm 0.1.1.0, 1y")])))
        True
        """
        if not all(axiom == step.name_str for axiom, step in zip(self.axioms, steps)):
            return False
        return all(AxSeqTreePos.remove_prefix(steps[i].head_idx, steps[i+1].head_idx) == self.rel_pos[i] for i in range(len(self.rel_pos)))

    def __str__(self):
        try:
            return f"{self.name_str} {self.pos_str}"
        except AttributeError:
            self.name_str = '~'.join(self.axioms)
            self.pos_str = '~'.join('$' if pos is None else pos for pos in self.rel_pos)
            return f"{self.name_str} {self.pos_str}"

    def __repr__(self):
        return f"AxSeqTreePos({self.axioms}, {self.rel_pos})"

    def __eq__(self, other):
        return self.axioms == other.axioms and self.rel_pos == other.rel_pos

    def __hash__(self):
        return hash(self.axioms) + hash(self.rel_pos)


if __name__ == "__main__":
    doctest.testmod()
