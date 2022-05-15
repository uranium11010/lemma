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
    >>> step
    Step("sub~{refl~comm} $~{$~1}, y~{$~2x}")
    >>> step.idx[1]
    (None, '1')
    >>> step.head_idx
    '1'
    >>> step2 = Step("sub~{refl~comm} $~{$~1}, y~{$~2x}")
    >>> step.idx
    (None, (None, '1'))
    >>> step2
    Step("sub~{refl~comm} $~{$~1}, y~{$~2x}")
    >>> step2.steps
    (AxStep("sub y"), Step("refl~comm $~1, $~2x"))
    """

    def __init__(self, arg):
        if isinstance(arg, (list, tuple)):
            assert all(isinstance(step, (AxStep, Step)) for step in arg)
            self.steps = tuple(step for step in arg)
            
            def wrap_brkt(string, step):
                if isinstance(step, Step):
                    wrap = False
                    cur_step = step
                    while isinstance(cur_step, Step):
                        if len(cur_step.steps) > 1:
                            wrap = True
                            break
                        cur_step = cur_step.steps[0]
                    if wrap:
                        return '{' + string + '}'
                return string

            self.name = tuple(step.name for step in self.steps)
            self.name_str = '~'.join(wrap_brkt(step.name_str, step) for step in self.steps)

            self.idx = tuple(step.idx for step in self.steps)
            self.idx_str = '~'.join(wrap_brkt(step.idx_str, step) for step in self.steps)

            self.param = tuple(step.param for step in self.steps)
            self.param_str = '~'.join(wrap_brkt(step.param_str, step) for step in self.steps)

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

            self.name = Step.split_to_tree(self.name_str)
            self.idx = Step.split_to_tree(self.idx_str, lambda x: None if x == '$' else x)
            self.param = Step.split_to_tree(self.param_str, lambda x: None if x == '$' else x)

            def get_step(name, idx, param):
                if not isinstance(name, tuple):
                    assert not isinstance(idx, tuple) and not isinstance(param, tuple)
                    return AxStep({"name": name, "idx": idx, "param": param})
                if isinstance(name, tuple):
                    assert isinstance(idx, tuple) and isinstance(param, tuple) and len(name) == len(idx) == len(param)
                    return Step([get_step(name[i], idx[i], param[i]) for i in range(len(name))])
                    
            self.steps = tuple(get_step(name, idx, param) for name, idx, param in zip(self.name, self.idx, self.param))

        else:
            raise TypeError("Arguments to Step must be list, tuple, str, or dict")

        self.head_idx = None
        for step in self.steps:
            if step.head_idx is not None:
                self.head_idx = step.head_idx
                break

    @staticmethod
    def split_to_tree(string, transform=lambda x: x):
        """
        Parses tree given in `string` with curly braces
        Stores tree in nested tuple structure
        """
        brkt_map = {}  # maps '{' index to '}' index
        depth_map = {}  # maps depth to '{' index
        d = 0
        for i, c in enumerate(string):
            if c == '{':
                d += 1
                depth_map[d] = i
            elif c == '}':
                brkt_map[depth_map[d]] = i
                d -= 1
                if d < 0:
                    raise Exception("Mismatching brackets")
        if d > 0:
            raise Exception("Mismatching brackets")
    
        return Step.split_to_tree_helper(string, transform, brkt_map)
    
    @staticmethod
    def split_to_tree_helper(string, transform, brkt_map, i=-1):
        """
        Returns tuple of objects/tuples in string between indices i and brkt_map[i]
        string[i] should be '{'
        brkt_map maps '{' to '}'
        Default: parses entire string
        """
        def get_elts():
            # generator yielding the elements (strings/tuples)
            l = i + 1
            while True:
                if string[l] == '{':
                    r = brkt_map[l] + 1
                    yield Step.split_to_tree_helper(string, transform, brkt_map, l)
                else:
                    r = l
                    while r < len(string) and string[r] != '~' and string[r] != '}':
                        r += 1
                    yield transform(string[l:r])
                if r == len(string) or string[r] == '}':
                    break
                l = r + 1
        return tuple(get_elts())

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

    >>> sol = Solution({"problem": "2x = 3", "solution": [{"state": "2x = 3", "action": "assumption"}, {"state": "((x * 2) / 2) = (3 / 2)", "action": "div~assoc $~1, 2~2x * 1"}]})
    >>> sol.states
    ['2x = 3', '((x * 2) / 2) = (3 / 2)']
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
            sol.states = [step["state"] for step in solution]
            # list of Step objects (tuple of AxStep/Step objects)
            sol.actions = [Step(solution[i]["action"])
                                for i in range(1, len(solution))]

        elif len(args) == 2:
            states, actions = args
            sol.states = list(states)
            sol.actions = list(actions)

        else:
            raise TypeError("Wrong number of arguments to Solution")

        return sol

    def display_compressed(self):
        """
        Outputs compressed string with axioms and params
        DOESN'T WORK FOR NESTED ABSTRACTIONS
        """
        if len(self.actions) == 1:
            return str(self.actions[0].steps[0])
        return str(Step(self.actions))

    def __str__(self):
        return '\n'.join(self.states[i] + '\n\t' + str(self.actions[i]) for i in range(len(self.actions))) + '\n' + self.states[-1]

    def __repr__(self):
        return str(self)



if __name__ == "__main__":
    doctest.testmod()
