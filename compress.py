"""
Simple compression algorithm that finds common subsequences of actions and abstracts them.
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
                    axiom.idx = int(axiom.ax_str[i+1:j])
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
            self.idx = tuple(map(lambda idx : None if idx == '$' else int(idx), self.idx_str.split('~')))
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


class Abstraction:
    @staticmethod
    def new(consider_pos, steps):
        if consider_pos:
            return AxSeqRelPos(steps)
        return AxiomSeq(steps)

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

    def __init__(self, args):
        """
        Builds abstraction from list of Step objects or list of axioms
        """
        if all(isinstance(step, Step) for step in args):
            self.ex_steps = args
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

    def __init__(self, steps):
        """
        Builds abstraction from list of Step objects
        """
        self.ex_steps = steps
        self.freq = None
        self.axioms = tuple(step.name_str for step in steps)
        self.rel_pos = tuple(steps[i+1].head_idx - steps[i].head_idx
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
        return all(self.rel_pos[i] is None or steps[i+1].head_idx - steps[i].head_idx == self.rel_pos[i] for i in range(len(self.rel_pos)))

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


class Compress(object):
    def __init__(self, solutions, axioms, consider_pos=False, peek_pos=False):
        self.solutions = list(Solution(sol) for sol in solutions)

        self.num_ax = len(axioms)  # num of axioms
        self.axioms = axioms  # list of (names of) axioms
        self.axiom_index = {self.axioms[k]: k for k in range(self.num_ax)}  # dictionary mapping axiom names to their indices (as in the list self.axioms)
        self.new_axioms = self.axioms.copy()  # list containing axioms + additional actions as abstractions (called "new axioms")
        self.new_axiom_set = set(self.new_axioms)

        self.frequencies = None
        self.consider_pos = consider_pos
        self.peek_pos = peek_pos
    

    def abstract(self):
        """
        Returns list of Abstraction objects
        """
        raise NotImplementedError

    # OLD
    # def get_axiom_tuple(self, solution):
    #     """
    #     Get tuple of integers corresponding to axioms in solution
    #     solution: format in self.solutions[i]["solution"] (i.e. list of state-action pairs as dictionaries)
    #     """
    #     if self.get_ax_pos:
    #         return tuple((self.axiom_index.get(self.get_ax_name(solution[i]["action"])),
    #                       self.get_ax_pos(solution[i]["action"]))
    #                      for i in range(1, len(solution)))
    #     return tuple(self.axiom_index.get(self.get_ax_name(solution[i]["action"]))
    #                  for i in range(1, len(solution)))

    def abstract_step(self, solution, abs_len, abstractions):
        """
        In solution, abstract out the first length-'abs_len' subsequence that is an abstraction
        solution: Solution object
        """
        axiom_list = solution.actions  # list of Step objects
        for i in range(len(solution.actions)-abs_len+1):
            ax_subseq = axiom_list[i:i+abs_len]
            new_ax = Abstraction.new(self.consider_pos, ax_subseq)
            if new_ax in abstractions:
                if new_ax not in self.new_axiom_set:
                    new_states = solution.states[:i+1] + solution.states[i+abs_len:]
                    new_actions = solution.actions[:i] + (Step(ax_subseq),) + solution.actions[i+abs_len:]

                    return Solution(new_states, new_actions)

    
    def abstracted_sol(self, max_len, abstractions=None):
        """
        Get abstracted solutions from set of abstractions
        Format: same as self.solutions
        (i.e. tuple of Solution objects)
        """
        if abstractions is None:
            abstractions = self.abstract()
        
        self.new_axioms += abstractions
        abs_set = set(abstractions)
        self.new_axiom_set |= abs_set

        new_sols = self.solutions.copy()
        for abs_len in range(max_len, 1, -1):
            for i in range(len(new_sols)):
                # print("BEGIN", new_sol[1])
                while True:
                    res = self.abstract_step(new_sols[i], abs_len, abs_set)
                    if res is None:
                        break
                    else:
                        new_sols[i] = res
                        # print("ABS_LEN", abs_len, new_sol[1])
        
        return new_sols



# DEPRECATED
class CommonPairs(Compress):
    """
    Finds common (cur, next) action pairs among solutions and constructs corresponding
    digraph with these pairs as edges.
    Uses paths of this digraph as abstractions.
    """
    def __init__(self, solutions, axioms, get_ax_name, get_ax_param, thres=None):
        super().__init__(solutions, axioms, get_ax_name, get_ax_param)
        self.thres = thres

    def get_frequencies(self):
        """
        Gets frequencies of (current action, next action) pairs
        """
        frequencies = np.zeros((self.num_ax, self.num_ax), dtype=int)
        for i in range(len(self.solutions)):
            sol = self.solutions[i]["solution"]
            for step in range(1, len(sol)-1):
                action_cur = self.axiom_index[self.get_ax_name(sol[step]["action"])]
                action_next = self.axiom_index[self.get_ax_name(sol[step+1]["action"])]
                frequencies[action_cur, action_next] += 1
        self.frequencies = frequencies
        return frequencies


    @staticmethod
    def dfs(N, graph, cur, paths, visited, cur_paths):
        """
        Finds all paths in graph starting at 'cur' node
        Adds them to 'paths' (or augments existing paths)
        Indices of paths in 'paths' that 'cur' node belongs to are in 'cur_paths'
        Nodes in paths that led to 'cur' node are in 'visited'
        ATTENTION: NOT YET OPTIMIZED FOR WHEN MANY PATHS GO TO SAME NODE (i.e. dfs would be repeatedly called on that node)
        """
        copied_cur_paths = [paths[path_idx] for path_idx in cur_paths]
        # first_next = True
        for next in range(N):
            if graph[cur, next]:
                # COMMENT OUT THIS IF STATEMENT IF YOU WANT PATHS LIKE [5, 8, 5] INSEAD OF [5, 8] FOR CYCLES
                if next in visited:
                    warnings.warn("Note: the graph has cycles")
                    continue

                # if first_next:
                #     for path_idx in cur_paths:
                #         paths[path_idx] = paths[path_idx] + (next,)
                #     next_paths = cur_paths
                #     first_next = False
                # else:
                next_paths = []
                for cur_path in copied_cur_paths:
                    paths.append(cur_path + (next,))
                    next_paths.append(len(paths)-1)
                
                # UNCOMMENT THIS PART IF YOU WANT PATHS LIKE [5, 8, 5] INSEAD OF [5, 8] FOR CYCLES
                # if next in visited:
                #     warnings.warn("Note: the graph has cycles")
                #     continue
                
                new_visited = visited.copy()
                new_visited.add(next)
                CommonPairs.dfs(N, graph, next, paths, new_visited, next_paths)


    @staticmethod
    def maximal_paths(N, graph):
        """
        Helper for common_subseq(..)
        Finds maximal paths in directed graph given by adjacency matrix 'graph'; N = # nodes
        ATTENTION: NOT 'MAXIMAL' IN THE REVERSE DIRECTION (SO IF [2, 5, 3, 5] IS DETECTED, [5, 3, 5] ALSO WOULD BE),
        HENCE THERE ARE MANY REDUNDANCIES
        """
        paths = []
        for node in range(N):
            paths.append((node,))
            CommonPairs.dfs(N, graph, node, paths, {node}, [len(paths)-1])
        
        return set(paths)


    def abstract(self, draw=False):
        """
        Finds common subsequences among solutions where any (current action, next action)
        pair within subsequence appears with frequency >= thres in dataset of solutions
        """
        thres = self.num_ax**(-0.75) if self.thres is None else self.thres # -0.75 is just an arbitrary number between -1 and 0 that I chose
        thres = int(np.ceil(len(solutions) * thres))
        graph = self.get_frequencies() >= thres

        if draw:
            print(graph.astype(int))
            util.draw_graph(self.num_ax, graph)

        return CommonPairs.maximal_paths(self.num_ax, graph)




class IterAbsPairs(Compress):
    def __init__(self, solutions, axioms, thres, top, consider_pos=False, peek_pos=False):
        super().__init__(solutions, axioms, consider_pos, peek_pos)
        self.thres = thres
        self.top = top


    def get_frequencies(self):
        """
        Gets frequencies of (current action, next action) pairs
        Also stores example abstraction for each rel. pos. if --peek
        """
        frequencies = {}
        for i in range(len(self.solutions)):
            sol = self.solutions[i]
            for j in range(len(sol.actions)-1):
                abstract = Abstraction.new(self.consider_pos, sol.actions[j:j+2])
                if not self.peek_pos or self.consider_pos:
                    if abstract in frequencies:
                        frequencies[abstract] += 1
                    else:
                        frequencies[abstract] = 1
                else:
                    wp_abs = Abstraction.new(True, sol.actions[j:j+2])
                    with_pos, wp_ex_steps = wp_abs.rel_pos, wp_abs.ex_steps
                    if abstract in frequencies:
                        frequencies[abstract][0] += 1
                        if with_pos in frequencies[abstract][1]:
                            frequencies[abstract][1][with_pos] += 1
                        else:
                            frequencies[abstract][1][with_pos] = 1
                            frequencies[abstract][2][with_pos] = wp_ex_steps
                    else:
                        frequencies[abstract] = [1, {with_pos: 1}, {with_pos: wp_ex_steps}]
        self.frequencies = frequencies
        return frequencies


    def abstract(self):
        """
        Finds common length-2 subsequences (current action, next action)
        that appear with frequency >= thres in dataset of solutions
        """
        if self.thres is None:
            thres = self.num_ax**(-0.75) if self.top is None else 0 # -0.75 is just an arbitrary exponent that's intuitive
        else:
            thres = self.thres
        thres = int(np.ceil(len(solutions) * thres))

        frequencies = self.get_frequencies()
        pairs = []
        for pair, freq in frequencies.items():
            if self.peek_pos:
                if freq[0] >= thres:
                    pairs.append((freq[0], pair, freq[1], freq[2]))
            else:
                if freq >= thres:
                    pairs.append((freq, pair))

        pairs.sort(reverse=True)
        top_pairs = pairs[:self.top]
        top_abs = []
        if self.peek_pos:
            for freq, pair, rel_pos_freq, rel_pos_ex_steps in top_pairs:
                pair.freq = freq / len(solutions)
                pair.rel_pos_freq = {rel_pos: pfreq / len(solutions) for rel_pos, pfreq in rel_pos_freq.items()}
                pair.rel_pos_ex_steps = rel_pos_ex_steps
                top_abs.append(pair)
        else:
            for freq, pair in top_pairs:
                pair.freq = freq / len(solutions)
                top_abs.append(pair)
        return top_abs
    

    def iter_abstract(self, K):
        """
        Abstract common (cur, next) pairs iteratively K times
        """
        sols = self.solutions
        axioms = self.axioms
        for _ in range(K):
            abstractor = IterAbsPairs(sols, axioms, self.thres, self.top, self.consider_pos, self.peek_pos)
            sols = abstractor.abstracted_sol(2)
            axioms = abstractor.new_axioms
        
        return sols, axioms




if __name__ == "__main__":
    solutions = util.load_solutions("equations-8k.json")
    _, axioms = util.load_axioms("equation_axioms.json")

    parser = argparse.ArgumentParser(description="Find mathematical absractions.")
    parser.add_argument("-t", dest="test", action="store_true", help="Testing")
    parser.add_argument("--file", type=str, help="File to store the abstractions")
    parser.add_argument("--iter", type=int, default=1, help="How many times to iterate pair abstraction process")
    parser.add_argument("--thres", type=float, default=None, help="Threshold frequency for abstractions")
    parser.add_argument("--top", metavar="K", type=int, default=None, help="Choose top K abstractions")
    parser.add_argument("-p", dest="consider_pos", action="store_true", help="Consider relative positions of application")
    parser.add_argument("--peek", dest="peek_pos", action="store_true", help="Take peek at relative positions even when we don't consider them")
    parser.add_argument("-v", dest="verbose", action="store_true", help="Display example axioms")

    args = parser.parse_args()
    if args.test:
        doctest.testmod()
    else:
        compressor = IterAbsPairs(solutions, axioms, args.thres, args.top, args.consider_pos, args.peek_pos)
        _, abs_ax = compressor.iter_abstract(args.iter)
        if args.file is not None:
            abs_ax_str = list(map(str, abs_ax))
            with open(args.file, "w") as f:
                json.dump({"num": len(abs_ax_str), "axioms": abs_ax_str}, f)
        else:
            if args.consider_pos or not args.peek_pos:
                for i in range(len(axioms), len(abs_ax)):
                    print(f"{str(abs_ax[i])}\n\t{abs_ax[i].freq}")
                    if args.verbose:
                        print('\tEx.  ', '   '.join(map(str, abs_ax[i].ex_steps)))
            else:
                for i in range(len(axioms), len(abs_ax)):
                    print(str(abs_ax[i]))
                    sorted_rel_pos = sorted(((freq, rp) for rp, freq in abs_ax[i].rel_pos_freq.items()), reverse=True)
                    for freq, rp in sorted_rel_pos:
                        print(f"\t{', '.join(map(str, rp))}\n\t\t{freq}")
                        if args.verbose:
                            print('\t\tEx.  ', '   '.join(map(str, abs_ax[i].rel_pos_ex_steps[rp])))

    # ex_sol = abs_sol[59]
    # util.print_solution(ex_sol)

