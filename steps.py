"""
Classes related to steps, axioms, and solutions
"""

import json
import numpy as np
import warnings
import argparse

import util

import doctest


class AxStep:
    """
    Single-axiom action

    >>> AxStep(AxStep("comm 3, (x + 2)")).param
    '(x + 2)'
    >>> print(AxStep("refl").idx)
    None
    >>> str(AxStep("sub 1"))
    'sub 1'
    >>> str(AxStep({"name": "comm", "idx": 3, "param": "(x + 2)"}))
    'comm 3, (x + 2)'
    """

    def __new__(cls, arg):
        if isinstance(arg, AxStep):
            return arg

        axiom = super(AxStep, cls).__new__(cls)
        if isinstance(arg, str):
            axiom.ax_str = arg

            i = axiom.ax_str.find(' ')
            if i == -1:
                axiom.name = axiom.ax_str
                axiom.idx = None
                axiom.param = None
            else:
                axiom.name = axiom.ax_str[:i]
                j = axiom.ax_str.find(',')
                if j == -1:
                    axiom.idx = None
                    axiom.param = axiom.ax_str[i+1:]
                else:
                    axiom.idx = axiom.ax_str[i+1:j]
                    axiom.param = axiom.ax_str[j+2:]

            axiom.head_idx = axiom.idx
                
        elif isinstance(arg, dict):
            axiom.name = arg["name"]
            axiom.idx = arg.get("idx")
            axiom.head_idx = axiom.idx
            axiom.param = arg.get("param")

        else:
            raise TypeError("Wrong arguments to AxStep")

        axiom.name_str = axiom.name
        axiom.idx_str = '$' if axiom.idx is None else str(axiom.idx)
        axiom.param_str = '$' if axiom.param is None else axiom.param

        return axiom

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
    >>> repr(step)
    'Step("sub~refl~comm $~$~1, y~$~2x")'
    >>> repr(Step("sub~refl~comm $~$~1, y~$~2x"))
    'Step("sub~refl~comm $~$~1, y~$~2x")'
    >>> step.idx[1]
    (None, 1)
    >>> step.head_idx
    1
    """

    def __init__(self, arg):
        if isinstance(arg, (list, tuple)):
            assert all(isinstance(step, (AxStep, Step)) for step in arg)
            self.steps = tuple(step for step in arg)

            self.name = tuple(step.name for step in self.steps)
            self.name_str = '~'.join(step.name_str for step in self.steps)

            self.idx = tuple(step.idx for step in self.steps)
            self.idx_str = '~'.join(step.idx_str for step in self.steps)

            self.param = tuple(step.param for step in self.steps)
            self.param_str = '~'.join(step.param_str for step in self.steps)

            for step in self.steps:
                i = step.head_idx
                if i is not None:
                    break
            self.head_idx = i
            

        elif isinstance(arg, str):
            if '~' not in arg:
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

            self.name = tuple(self.name_str.split('~'))
            self.idx = tuple(map(lambda idx : None if idx == '$' else idx, self.idx_str.split('~')))
            self.param = tuple(map(lambda param : None if param == '$' else param, self.param_str.split('~')))

            self.steps = tuple(AxStep({"name": name, "idx": idx, "param": param}) for name, idx, param in zip(self.name, self.idx, self.param))

            for step in self.steps:
                idx = step.head_idx
                if idx is not None:
                    break
            self.head_idx = idx

        else:
            raise TypeError("Arguments to Step must be list, tuple, or str")

    def __str__(self):
        try:
            return self.step_str
        except AttributeError:
            self.step_str = f"{self.name_str} {self.idx_str}, {self.param_str}"
            return self.step_str

    def __repr__(self):
        return f"Step(\"{str(self)}\")"

    def __iter__(self):
        for step in self.steps:
            if isinstance(step, AxStep):
                yield step
            else:
                yield from step

    def __lt__(self, other):
        return False
        

class Solution:
    """
    Solution stored as tuple of states (strings) and tuple of Step object

    >>> sol = Solution([{"state": "2x = 3", "action": "assumption"}, {"state": "((x * 2) / 2) = (3 / 2)", "action": "div~assoc $~1, 2~2x * 1"}])
    >>> sol.states
    ('2x = 3', '((x * 2) / 2) = (3 / 2)')
    >>> sol.actions[0].steps[1].param
    '2x * 1'
    >>> sol.actions[0].steps
    (AxStep("div 2"), AxStep("assoc 1, 2x * 1"))
    """

    def __new__(cls, *args):
        if isinstance(args[0], Solution) and len(args) == 1:
            return args[0]

        sol = super(Solution, cls).__new__(cls)
        if len(args) == 1:
            """
            solution: {"problem": <str>, "solution": [{"state": <str>, "action": <str>}, ...]}
            """
            solution = args[0]["solution"]
            # list of string of states
            sol.states = tuple(step["state"] for step in solution)
            # list of Step objects (tuple of AxStep/Step objects)
            sol.actions = tuple(Step(solution[i]["action"])
                                for i in range(1, len(solution)))

        elif len(args) == 2:
            """
            solution: [{"state": <str>, "action": <str>}, ...] 
            """
            states, actions = args
            sol.states = tuple(states)
            sol.actions = tuple(actions)

        else:
            raise TypeError("Wrong number of arguments to Solution")

        return sol
