"""
Classes related to steps, axioms, and solutions
"""

import json
import numpy as np
import warnings
import argparse

from abstractions import *
import abs_util

import doctest


class AxStep:
    """
    Single-axiom action

    >>> AxStep("comm 3, (x + 2)").param
    '(x + 2)'
    >>> print(AxStep("refl").idx)
    None
    >>> str(AxStep("sub 1"))
    'sub 1'
    >>> str(AxStep({"name": "comm", "idx": 3, "param": "(x + 2)"}))
    'comm 3, (x + 2)'
    """

    def __init__(self, arg):
        if isinstance(arg, str):
            self.ax_str = arg

            i = self.ax_str.find(' ')
            if i == -1:
                self.name = self.ax_str
                self.idx = None
                self.param = None
            else:
                self.name = self.ax_str[:i]
                j = self.ax_str.find(',')
                if j == -1:
                    self.idx = None
                    self.param = self.ax_str[i+1:]
                else:
                    self.idx = self.ax_str[i+1:j]
                    self.param = self.ax_str[j+2:]
                
        elif isinstance(arg, dict):
            self.name = arg["name"]
            self.idx = arg.get("idx")
            self.param = arg.get("param")

        else:
            raise TypeError("Wrong arguments to AxStep")

        self.head_idx = self.idx
        self.tail_idx = self.idx

        self.name_str = self.name
        self.idx_str = '$' if self.idx is None else str(self.idx)
        self.param_str = '$' if self.param is None else self.param

    def __len__(self):
        return 1

    def __str__(self):
        try:
            return self.ax_str
        except AttributeError:
            if self.param is None:
                self.ax_str = self.name
            elif self.idx is None:
                self.ax_str = f"{self.name} {self.param}"
            else:
                self.ax_str = f"{self.name} {self.idx}, {self.param}"
            return self.ax_str

    def __repr__(self):
        return f"AxStep(\"{str(self)}\")"


class Step:
    """
    Tuple of AxStep and Step objects

    >>> step = Step([AxStep({"name": "sub", "param": "y"}), Step("refl~comm $~1, $~2x")])
    >>> step
    Step("sub~{refl~comm} $~{$~1}, y~{$~2x}")
    >>> step.idx[1]
    (None, '1')
    >>> step.tail_idx
    '1'
    >>> step.flat_steps
    (AxStep("sub y"), AxStep("refl"), AxStep("comm 1, 2x"))
    >>> step2 = Step("sub~{refl~comm} $~{$~1}, y~{$~2x}")
    >>> step.idx
    (None, (None, '1'))
    >>> step2
    Step("sub~{refl~comm} $~{$~1}, y~{$~2x}")
    >>> step2.steps
    (AxStep("sub y"), Step("refl~comm $~1, $~2x"))
    >>> len(step2)
    3
    """

    def __init__(self, arg, ex_states=None, abs_type=AxSeqTreePos):
        self.ex_states = ex_states
        if hasattr(self.ex_states, "__iter__"):
            self.ex_states = tuple(self.ex_states)

        if isinstance(arg, str):
            if ',' not in arg:
                ax_repr = AxStep(arg)

                self.name_str = ax_repr.name_str
                self.idx_str = ax_repr.idx_str
                self.param_str = ax_repr.param_str
            
            else:
                i = arg.find(' ')
                j = arg.find(',')
                self.name_str = arg[:i]
                self.idx_str = arg[i+1:j]
                self.param_str = arg[j+2:]

            def transform(x):
                if isinstance(x, str):
                    return None if x == '$' else x
                else:
                    return tuple(x)
            self.name = abs_util.split_to_tree(self.name_str, transform=transform)
            self.idx = abs_util.split_to_tree(self.idx_str, transform=transform)
            self.param = abs_util.split_to_tree(self.param_str, transform=transform)

            def get_step(name, idx, param):
                if not isinstance(name, tuple):
                    assert not isinstance(idx, tuple) and not isinstance(param, tuple)
                    return AxStep({"name": name, "idx": idx, "param": param})
                if isinstance(name, tuple):
                    assert isinstance(idx, tuple) and isinstance(param, tuple) and len(name) == len(idx) == len(param)
                    return Step([get_step(name[i], idx[i], param[i]) for i in range(len(name))])
                    
            self.steps = tuple(get_step(name, idx, param) for name, idx, param in zip(self.name, self.idx, self.param))

        elif hasattr(arg, "__iter__"):
            self.steps = tuple(arg)
            assert all(isinstance(step, (AxStep, Step)) for step in self.steps)

            def wrap_brkt(string, step):
                if len(step) > 1:
                    return '{' + string + '}'
                return string

            self.name = tuple(step.name for step in self.steps)
            self.name_str = '~'.join(wrap_brkt(step.name_str, step) for step in self.steps)

            self.idx = tuple(step.idx for step in self.steps)
            self.idx_str = '~'.join(wrap_brkt(step.idx_str, step) for step in self.steps)

            self.param = tuple(step.param for step in self.steps)
            self.param_str = '~'.join(wrap_brkt(step.param_str, step) for step in self.steps)

        else:
            raise TypeError("Arguments to Step must be list, tuple, str, or dict")

        self.length = sum(len(step) for step in self.steps)
        self.flat_steps = sum(((step,) if isinstance(step, AxStep) else step.flat_steps for step in self.steps), ())

        self.head_idx = self.flat_steps[0].idx
        self.tail_idx = self.flat_steps[-1].idx

        self.abstraction = abs_type(self.steps, ex_states)

    def __len__(self):
        return self.length

    def __str__(self):
        try:
            return self.step_str
        except AttributeError:
            self.step_str = f"{self.name_str} {self.idx_str}, {self.param_str}"
            return self.step_str

    def __repr__(self):
        return f"Step(\"{str(self)}\")"

    def __iter__(self):
        """
        Iterates through all AxStep objects
        """
        for step in self.steps:
            if isinstance(step, AxStep):
                yield step
            else:
                yield from step

    def __lt__(self, other):
        return False


class Solution:
    """
    Solution stored as tuple of states (strings) and tuple of Step objects

    >>> sol = Solution({"problem": "2x = 3", "solution": [{"state": "2x = 3", "action": "assumption"}, {"state": "((x * 2) / 2) = (3 / 2)", "action": "div~assoc $~1, 2~2x * 1"}]})
    >>> sol.states
    ['2x = 3', '((x * 2) / 2) = (3 / 2)']
    >>> sol.actions[0].steps[1].param
    '2x * 1'
    >>> sol.actions[0].steps
    (AxStep("div 2"), AxStep("assoc 1, 2x * 1"))
    """

    def __init__(self, *args):
        if len(args) == 1:
            """
            solution: {"problem": <str>, "solution": [{"state": <str>, "action": <str>}, ...]}
            """
            solution = args[0]["solution"]
            # list of string of states
            self.states = [step["state"] for step in solution]
            # list of Step objects (tuple of AxStep/Step objects)
            self.actions = [Step(solution[i]["action"], ex_states=self.states[i-1:i+1])
                                for i in range(1, len(solution))]

        elif len(args) == 2:
            states, actions = args
            self.states = list(states)
            self.actions = list(actions)

        else:
            raise TypeError("Wrong number of arguments to Solution")

    def display_compressed(self):
        """
        Outputs compressed string with axioms and params (no states)
        Equivalent to string of corresponding Step/AxStep object
        """
        if len(self.actions) == 1:
            step = self.actions[0]
            while isinstance(step, Step):
                step = step.steps[0]
            return str(step)
        return str(Step(self.actions))

    def __str__(self):
        return '\n'.join(self.states[i] + '\n\t' + str(self.actions[i]) for i in range(len(self.actions))) + '\n' + self.states[-1]

    def __repr__(self):
        return str(self)



if __name__ == "__main__":
    doctest.testmod()
