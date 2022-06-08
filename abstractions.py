"""
Classes for types of abstractions
"""

import json
import numpy as np
import warnings
import argparse

from steps import *
import abs_util

import doctest


class Abstraction:
    @staticmethod
    def new(config, arg, ex_states=None):
        if config.get("tree_idx", False):
            return AxSeqTreePos(arg, ex_states)
        if config.get("consider_pos", False):
            return AxSeqRelPos(arg, ex_states)
        return AxiomSeq(arg, ex_states)

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

    @staticmethod
    def get_abs_elt(next_step, cur_steps):
        """
        Gets abstraction element corresponding to `next_step`, given `cur_steps`
        """
        raise NotImplementedError()

    def __iter__(self):
        """
        Allows iteration through the constituents of the abstraction
        """
        raise NotImplementedError()

    def __len__(self):
        return self.length

    def __lt__(self, other):
        # to make sorting work when getting top-frequency abstractions
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
            return f"{self.name_str}:{self.pos_str}"
        except AttributeError:
            self.name_str = '~'.join(self.axioms)
            self.pos_str = '~'.join('$' if pos is None else str(pos) for pos in self.rel_pos)
            return f"{self.name_str}:{self.pos_str}"

    def __repr__(self):
        return f"AxSeqRelPos({self.axioms}, {self.rel_pos})"

    def __eq__(self, other):
        return self.axioms == other.axioms and self.rel_pos == other.rel_pos

    def __hash__(self):
        return hash(self.axioms) + hash(self.rel_pos)


class AxSeqTreePos(Abstraction):
    """
    Abstraction: sequence of axioms + relative positions of application within tree
    DOES NOT SUPPORT ABSTRACTIONS OF ABSTRACTIONS (3rd test case will fail)

    >>> AxSeqTreePos([Step("refl"), Step((AxStep("sub 1"), Step("comm 0.0.1, 3x"))), Step("comm 0.1, 2x")]).rel_pos
    ((None, None), ('0.1', '1'))
    >>> AxSeqTreePos("assoc~eval:_1").rel_pos
    (('', '1'),)
    >>> print(AxSeqTreePos("{{sub~{assoc~eval:_1}:$_0.0}~eval:0_1}~{comm~{{div~{assoc~eval:_1}:$_0.0}~{mul1~eval:0_1}:_}:_}:_").axioms[0].axioms)
    (AxSeqTreePos("sub~{assoc~eval:_1}:$_0.0"), 'eval')
    """

    def __init__(self, arg, ex_states=None):
        """
        Builds abstraction from list of Step objects or a string representation of the abstraction
        step.head_idx and step.tail_idx are bits
        """
        self.ex_states = ex_states
        if hasattr(self.ex_states, "__iter__"):
            self.ex_states = tuple(self.ex_states)
        self.freq = None

        done_init = False
        if isinstance(arg, str):
            if '~' not in arg:
                self.axioms = (arg,)
                self.rel_pos = ()
                self.ex_steps = None
                done_init = True
            else:
                arg = abs_util.split_to_tree(arg, transform=lambda x, info=None: x if isinstance(x, str) else {"axioms": [elt if isinstance(elt, str) else AxSeqTreePos(elt) for elt in x], "info": info}, info_mark=':')
            """
            k = arg.find(':')
            if k == -1:
                self.axioms = (arg,)
                self.rel_pos = ()
            else:
                ax_str = arg[:k]
                pos_str = arg[k+1:]
                self.axioms = tuple(ax_str.split('~'))
                split_pos_str = pos_str.split('~')
                self.rel_pos = tuple(tuple(map(lambda x: None if x == '$' else x, pos.split('_'))) for pos in split_pos_str)
            """

        if not done_init:
            if isinstance(arg, dict):
                # "axioms": list of Abstraction objects or strings; "info": string containing rel. pos. info
                self.axioms = tuple(arg["axioms"])
                split_pos_str = arg["info"].split('~')
                self.rel_pos = tuple(tuple(map(lambda x: None if x == '$' else x, pos.split('_'))) for pos in split_pos_str)
                self.ex_steps = None

            else:
                self.ex_steps = arg
                def get_axioms():
                    for step in arg:
                        if len(step) == 1:
                            yield step.name_str
                        elif hasattr(step, "abstraction"):
                            yield step.abstraction
                        else:
                            warnings.warn("Step object doesn't have abstraction attribute")
                            ab = AxSeqTreePos(step.steps)
                            step.abstraction = ab
                            yield ab
                self.axioms = tuple(get_axioms())
                self.rel_pos = tuple(AxSeqTreePos.remove_prefix(arg[i].tail_idx, arg[i+1].head_idx)
                                     for i in range(len(arg)-1))

        self.length = sum(1 if isinstance(ax, str) else len(ax) for ax in self.axioms)
        self.height = 1 + max((0 if isinstance(ax, str) else ax.height) for ax in self.axioms)

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
                i = 0
                while i < len(idx1) and i < len(idx2) and idx1[i] == idx2[i]:
                    i += 2  # specifically for bit string including periods separating indicees
                return idx1[i:], idx2[i:]

    def has_instance(self, steps):
        """
        NOT USED
        >>> seq = AxSeqTreePos([Step("eval 0.1, 2/2"), Step([Step("sub~comm $~0.0, 1~3x")])])
        >>> seq.within((Step("refl~refl $~$, $~$"), Step("eval 0.0.1, 1/5"), Step([Step("sub 1"), AxStep("comm 0.1.1.1, 1y")])))
        False
        >>> seq.within((Step("refl~refl $~$, $~$"), Step("eval 0.1.1.1, 1/5"), Step([Step("sub 1"), AxStep("comm 0.1.1.0, 1y")])))
        True
        """
        if not all(axiom == step.name_str for axiom, step in zip(self.axioms, steps)):
            return False
        return all(AxSeqTreePos.remove_prefix(steps[i].head_idx, steps[i+1].head_idx) == self.rel_pos[i] for i in range(len(self.rel_pos)))

    @staticmethod
    def get_abs_elt(next_step, cur_steps):
        """
        >>> AxSeqTreePos.get_abs_elt(Step("eval 0.0.0.1, 3 - 3"), Solution(["", ""], [Step("assoc 0.0.0, (x + 3) - 3")]))
        (('', '1'), 'eval')
        """
        if len(cur_steps.actions) == 0:
            return next_step.name[0]
        last_step = cur_steps.actions[-1]
        return (AxSeqTreePos.remove_prefix(last_step.tail_idx, next_step.head_idx), next_step.name[0])

    def __iter__(self, prev_rel_pos=None):
        """
        >>> seq = AxSeqTreePos("comm~assoc~{eval~comm:1_}~{sub~eval:$_0.1}:0_~_1~0_$")
        >>> for elt in seq:
        ...     print(elt)
        ...
        comm
        (('0', ''), 'assoc')
        (('', '1'), 'eval')
        (('1', ''), 'comm')
        (('0', None), 'sub')
        ((None, '0.1'), 'eval')
        """
        if prev_rel_pos is None:
            yield self.axioms[0]
        else:
            yield (prev_rel_pos, self.axioms[0])
        for i in range(1, len(self.axioms)):
            if isinstance(self.axioms[i], str):
                yield (self.rel_pos[i-1], self.axioms[i])
            else:
                assert isinstance(self.axioms[i], AxSeqTreePos)
                yield from self.axioms[i].__iter__(self.rel_pos[i-1])
                
    def __str__(self):
        if hasattr(self, "name_str") and hasattr(self, "pos_str"):
            return f"{self.name_str}:{self.pos_str}"
        def get_name_str(ax):
            if isinstance(ax, str):
                return ax
            else:
                return '{' + str(ax) + '}'
        self.name_str = '~'.join(map(get_name_str, self.axioms))
        def get_pos_str(pos):
            str1 = '$' if pos[0] is None else pos[0]
            str2 = '$' if pos[1] is None else pos[1]
            return str1 + '_' + str2
        self.pos_str = '~'.join(map(get_pos_str, self.rel_pos))
        if self.pos_str:
            return f"{self.name_str}:{self.pos_str}"
        return self.name_str

    def __repr__(self):
        return f'AxSeqTreePos("{str(self)}")'

    def __eq__(self, other):
        return isinstance(other, AxSeqTreePos) and self.axioms == other.axioms and self.rel_pos == other.rel_pos

    def __hash__(self):
        return hash(self.axioms) + hash(self.rel_pos)


if __name__ == "__main__":
    doctest.testmod()
