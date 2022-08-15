"""
Classes for types of abstractions
"""

import json
import numpy as np
import warnings
import argparse

import abs_util

import doctest

class Rule:
    @staticmethod
    def from_string(rule_str, abs_type=None):
        if '~' not in rule_str:
            assert abs_type is None
            return Axiom(rule_str)
        else:
            assert abs_type is not None
            if abs_type == "tree_rel_pos":
                return AxSeqTreeRelPos.from_string(rule_str)
            if abs_type == "dfs_idx_rel_pos":
                return AxSeqDfsIdxRelPos.from_string(rule_str)
            if abs_type == "ax_seq":
                return AxiomSeq.from_string(rule_str)
            raise Exception("Invalid abstraction type")


class Axiom(Rule):
    def __init__(self, name):
        self.name = name
        self.height = 0

    def __len__(self):
        return 1

    def __str__(self):
        return self.name
    
    def __repr__(self):
        return f"Axiom(\"{self.name}\")"

    def __eq__(self, other):
        return isinstance(other, Axiom) and self.name == other.name

    def __hash__(self):
        return hash(self.name)


class Abstraction(Rule):
    def __init__(self, rules, ex_step=None, ex_states=None):
        assert isinstance(rules, (list, tuple))
        assert len(rules) > 1
        assert all(isinstance(rule, Rule) for rule in rules)
        self.rules = tuple(rules)
        self.ex_step = ex_step
        self.ex_states = None if ex_states is None else tuple(ex_states)
        self.ex_steps = None  # only for initializing with `from_steps` method

        self.length = sum(len(rule) for rule in self.rules)
        self.height = 1 + max(rule.height for rule in self.rules)

        self.freq = None
        self.score = None

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
        num_ax = len(self.rules)
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
    Abstraction: sequence of rules

    >>> from steps import *; from abstractions import *
    >>> AxiomSeq([Step.from_string("refl"), AbsStep([Step.from_string("sub~comm $~3, 1~3x"), Step.from_string("comm 2, 2x")])]).rules
    ('refl', 'sub~comm~comm')
    """

    def __init__(self, args, ex_states=None):
        """
        Builds abstraction from list of Step objects or list of rules
        """
        if all(isinstance(step, Step) for step in args):
            self.ex_steps = args
            self.ex_states = ex_states
            self.rules = tuple(step.name_str for step in args)
        elif all(isinstance(step_name, str) for step_name in args):
            self.rules = tuple(args)
        self.freq = None
        self.rel_pos_freq = None
        self.rel_pos_ex_steps = None

    def has_instance(self, steps):
        """
        >>> from steps import Step, AbsStep
        >>> seq = AxiomSeq([Step.from_string("refl"), Step.from_string("sub~comm $~3, 1~3x")])
        >>> seq.within((Step.from_string("refl~refl $~$, $~$"), Step.from_string("refl"), AbsStep([Step.from_string("sub 1"), Step.from_string("comm 6, 1y")])))
        True
        """
        return all(axiom == step.name_str for axiom, step in zip(self.rules, steps))

    def __str__(self):
        try:
            return self.name_str
        except AttributeError:
            self.name_str = '~'.join(self.rules)
            return self.name_str

    def __repr__(self):
        return f"AxiomSeq{self.rules}"

    def __eq__(self, other):
        return self.rules == other.rules

    def __hash__(self):
        return hash(self.rules)


class AxSeqDfsIdxRelPos(Abstraction):
    """
    Abstraction: sequence of rules + relative positions of application
    DOES NOT FULLY SUPPORT NESTED ABSTRACTIONS (CURRENTLY LOSES POSITION INFO)

    >>> from steps import *; from abstractions import *
    >>> AxSeqDfsIdxRelPos([Step.from_string("refl"), AbsStep((Step.from_string("sub 1"), Step.from_string("comm 3, 3x"))), Step.from_string("comm 2, 2x")]).rel_pos
    (None, -1)
    """

    def __init__(self, steps, ex_states=None):
        """
        Builds abstraction from list of Step objects
        """
        self.ex_steps = steps
        self.ex_states = ex_states
        self.freq = None
        self.rules = tuple(step.name_str for step in steps)
        self.rel_pos = tuple(int(steps[i+1].head_idx) - int(steps[i].head_idx)
                             if steps[i+1].head_idx is not None and steps[i].head_idx is not None
                             else None
                             for i in range(len(steps)-1))


    def has_instance(self, steps):
        """
        >>> from steps import Step, AxStep, AbsStep
        >>> seq = AxSeqDfsIdxRelPos([Step.from_string("eval 3, 2/2"), Step.from_string("sub~comm $~3, 1~3x")])
        >>> seq.has_instance((Step.from_string("refl~refl $~$, $~$"), Step.from_string("eval 3, 1/5"), AbsStep([AxStep.from_string("sub 1"), AxStep.from_string("comm 6, 1y")])))
        False
        >>> seq.has_instance((Step.from_string("refl~refl $~$, $~$"), Step.from_string("eval 5, 1/5"), AbsStep([AxStep.from_string("sub 1"), AxStep.from_string("comm 5, 1y")])))
        True
        """
        if not all(axiom == step.name_str for axiom, step in zip(self.rules, steps)):
            return False
        return all(self.rel_pos[i] is None or int(steps[i+1].head_idx) - int(steps[i].head_idx) == self.rel_pos[i] for i in range(len(self.rel_pos)))

    def __str__(self):
        try:
            return f"{self.name_str}:{self.pos_str}"
        except AttributeError:
            self.name_str = '~'.join(self.rules)
            self.pos_str = '~'.join('$' if pos is None else str(pos) for pos in self.rel_pos)
            return f"{self.name_str}:{self.pos_str}"

    def __repr__(self):
        return f"AxSeqDfsIdxRelPos({self.rules}, {self.rel_pos})"

    def __eq__(self, other):
        return self.rules == other.rules and self.rel_pos == other.rel_pos

    def __hash__(self):
        return hash(self.rules) + hash(self.rel_pos)


class AxSeqTreeRelPos(Abstraction):
    """
    Abstraction: sequence of rules + relative positions of application within tree
    Corresponding Step objects have bit strings as their indices

    >>> from steps import *; from abstractions import *
    >>> AxSeqTreeRelPos.from_steps([Step.from_string("refl"), AbsStep((Step.from_string("sub 1"), Step.from_string("comm 0.0.1, 3x"))), Step.from_string("comm 0.1, 2x")]).rel_pos
    ((None, None), ('0.1', '1'))
    >>> AxSeqTreeRelPos.from_string("assoc~eval:_1").rel_pos
    (('', '1'),)
    >>> print(AxSeqTreeRelPos.from_string("{{sub~{assoc~eval:_1}:$_0.0}~eval:0_1}~{comm~{{div~{assoc~eval:_1}:$_0.0}~{mul1~eval:0_1}:_}:_}:_").rules[0].rules)
    (AxSeqTreeRelPos("sub~{assoc~eval:_1}:$_0.0"), Axiom("eval"))
    """

    def __init__(self, rules, rel_pos, ex_step=None, ex_states=None):
        super().__init__(rules, ex_step, ex_states)
        self.rel_pos = rel_pos
        
    @staticmethod
    def from_string(abs_str, ex_step=None, ex_states=None):
        def transform(component, info=None):
            if isinstance(component, str):
                return Axiom(component)
            split_pos_str = info.split('~')
            rel_pos = tuple(tuple(map(lambda x: None if x == '$' else x, pos.split('_'))) for pos in split_pos_str)
            return AxSeqTreeRelPos(component, rel_pos)
        abstraction = abs_util.split_to_tree(abs_str, transform=transform, info_mark=':')
        abstraction.ex_step = ex_step
        abstraction.ex_states = ex_states
        return abstraction

    @staticmethod
    def from_steps(steps, ex_step=None, ex_states=None):
        rules = tuple(step.rule for step in steps)
        rel_pos = tuple(AxSeqTreeRelPos.remove_prefix(steps[i].tail_idx, steps[i+1].head_idx)
                        for i in range(len(steps)-1))
        abstraction = AxSeqTreeRelPos(rules, rel_pos, ex_step, ex_states)
        abstraction.ex_steps = steps
        return abstraction

    @staticmethod
    def from_abs_elt(abs_elts, ex_step=None, ex_states=None):
        """
        See `get_abs_elt` and `__iter__` for specification for `abs_elts`

        >>> from abstractions import *
        >>> AxSeqTreeRelPos.from_abs_elt([(None, Axiom("hi")), (('', ''), Axiom("my")), (('1', '0'), Axiom("name")), (('0.1', '1'), Axiom("is")), (('1.0', '0.0'), Axiom("Zhening"))])
        AxSeqTreeRelPos("hi~my~name~is~Zhening:_~1_0~0.1_1~1.0_0.0")
        """
        rel_pos, rules = zip(*abs_elts)
        return AxSeqTreeRelPos(rules, rel_pos[1:], ex_step, ex_states)

    @staticmethod
    def from_shifted_abs_elt(abs_elts, ex_step=None, ex_states=None):
        """
        `abs_elts` are 'shifted' (see test case)

        >>> from abstractions import *
        >>> AxSeqTreeRelPos.from_shifted_abs_elt([(Axiom("hi"), ('', '')), (Axiom("my"), ('1', '0')), (Axiom("name"), ('0.1', '1')), (Axiom("is"), ('1.0', '0.0')), (Axiom("Zhening"), None)])
        AxSeqTreeRelPos("hi~my~name~is~Zhening:_~1_0~0.1_1~1.0_0.0")
        """
        rules, rel_pos = zip(*abs_elts)
        return AxSeqTreeRelPos(rules, rel_pos[:-1], ex_step, ex_states)

    @staticmethod
    def remove_prefix(idx1, idx2):
        """
        Given idx1 and idx2 (strings of bits), remove maximal common prefix
        """
        if idx1 is None:
            if idx2 is None:
                return None, None
            return None, idx2
        if idx2 is None:
            return idx1, None
        i = 0
        while i < len(idx1) and i < len(idx2) and idx1[i] == idx2[i]:
            i += 2  # specifically for bit string including periods separating indicees
        return idx1[i:], idx2[i:]

    def has_instance(self, steps):
        """
        NOT USED

        >>> from steps import *; from abstractions import *
        >>> abstraction = AxSeqTreeRelPos.from_steps([Step.from_string("eval 0.1, 2/2"), Step.from_string("comm~assoc 0.0.0~0.0, 3x~(x * 3) / 3")])
        >>> abstraction.has_instance((Step.from_string("eval 0.0.1, 1/5"), AbsStep([AxStep.from_string("comm 0.1.1.1, 1y"), AxStep.from_string("assoc 0.1.1, (x * 3) / 3")])))
        False
        >>> abstraction.has_instance((Step.from_string("eval 0.1.1.1, 1/5"), AbsStep([AxStep.from_string("comm 0.1.1.0.0, 1y"), AxStep.from_string("assoc 0.1.1.0, (y * 1) / 1")])))
        True
        """
        return self == AxSeqTreeRelPos.from_steps(steps)

    @staticmethod
    def get_abs_elt(next_step, cur_steps):
        """
        `cur_steps` is Solution object

        >>> from steps import Step, Solution
        >>> AxSeqTreeRelPos.get_abs_elt(Step.from_string("eval 0.0.0.1, 3 - 3"), Solution(["", ""], [Step.from_string("assoc 0.0.0, (x + 3) - 3")]))
        (('', '1'), Axiom("eval"))
        """
        if len(cur_steps.actions) == 0:
            return (None, next_step.rule)
        last_step = cur_steps.actions[-1]
        return (AxSeqTreeRelPos.remove_prefix(last_step.tail_idx, next_step.head_idx), next_step.rule)

    def __iter__(self, prev_rel_pos=None):
        """
        >>> seq = AxSeqTreeRelPos.from_string("comm~assoc~{eval~comm:1_}~{sub~eval:$_0.1}:0_~_1~0_$")
        >>> for elt in seq:
        ...     print(elt)
        ...
        (None, Axiom("comm"))
        (('0', ''), Axiom("assoc"))
        (('', '1'), Axiom("eval"))
        (('1', ''), Axiom("comm"))
        (('0', None), Axiom("sub"))
        ((None, '0.1'), Axiom("eval"))
        """
        if isinstance(self.rules[0], Axiom):
            yield (prev_rel_pos, self.rules[0])
        else:
            assert isinstance(self.rules[0], AxSeqTreeRelPos)
            yield from self.rules[0].__iter__(prev_rel_pos)
        for i in range(1, len(self.rules)):
            if isinstance(self.rules[i], Axiom):
                yield (self.rel_pos[i-1], self.rules[i])
            else:
                assert isinstance(self.rules[i], AxSeqTreeRelPos)
                yield from self.rules[i].__iter__(self.rel_pos[i-1])
                
    def __str__(self):
        if not hasattr(self, "name_str"):
            def get_name_str(rule):
                if isinstance(rule, Axiom):
                    return rule.name
                return '{' + str(rule) + '}'
            self.name_str = '~'.join(map(get_name_str, self.rules))
        if not hasattr(self, "pos_str"):
            def get_pos_str(pos):
                str1 = '$' if pos[0] is None else pos[0]
                str2 = '$' if pos[1] is None else pos[1]
                return str1 + '_' + str2
            self.pos_str = '~'.join(map(get_pos_str, self.rel_pos))
        return f"{self.name_str}:{self.pos_str}"

    def __repr__(self):
        return f'AxSeqTreeRelPos("{str(self)}")'

    def __eq__(self, other):
        return isinstance(other, AxSeqTreeRelPos) and self.rules == other.rules and self.rel_pos == other.rel_pos

    def __hash__(self):
        return hash(self.rules) ^ hash(self.rel_pos)


if __name__ == "__main__":
    doctest.testmod()
