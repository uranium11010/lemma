"""
Simple compression algorithm that finds common subsequences of actions and abstracts them.
"""

import json
import numpy as np
import warnings
import argparse

from steps import *
from abstractions import *
import util

import doctest


class Compress(object):
    def __init__(self, solutions, axioms, config):
        self.solutions = list(Solution(sol) for sol in solutions)

        self.num_ax = len(axioms)  # num of axioms
        self.axioms = axioms  # list of (names of) axioms
        self.axiom_index = {self.axioms[k]: k for k in range(self.num_ax)}  # dictionary mapping axiom names to their indices (as in the list self.axioms)
        self.new_axioms = self.axioms.copy()  # list containing axioms + additional actions as abstractions (called "new axioms")
        self.new_axiom_set = set(self.new_axioms)

        self.frequencies = None
        self.config = config
        self.consider_pos = config.get("consider_pos", False)
        self.peek_pos = config.get("peek_pos", False)
    

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
            new_ax = Abstraction.new(self.config, ax_subseq)
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
    def __init__(self, solutions, axioms, config):
        super().__init__(solutions, axioms, config)
        self.thres = config.get("thres")
        self.top = config.get("top")


    def get_frequencies(self):
        """
        Gets frequencies of (current action, next action) pairs
        Also stores example abstraction for each rel. pos. if --peek
        """
        frequencies = {}
        for i in range(len(self.solutions)):
            sol = self.solutions[i]
            for j in range(len(sol.actions)-1):
                abstract = Abstraction.new(self.config, sol.actions[j:j+2], sol.states[j:j+3])
                if not self.peek_pos or self.consider_pos:
                    if abstract in frequencies:
                        frequencies[abstract] += 1
                    else:
                        frequencies[abstract] = 1
                else:
                    wp_abs = Abstraction.new(self.config | {"consider_pos": True}, sol.actions[j:j+2], sol.states[j:j+3])
                    with_pos, wp_ex_steps, wp_ex_states = wp_abs.rel_pos, wp_abs.ex_steps, wp_abs.ex_states
                    if abstract in frequencies:
                        frequencies[abstract][0] += 1
                        if with_pos in frequencies[abstract][1]:
                            frequencies[abstract][1][with_pos] += 1
                        else:
                            frequencies[abstract][1][with_pos] = 1
                            frequencies[abstract][2][with_pos] = wp_ex_steps
                            frequencies[abstract][3][with_pos] = wp_ex_states
                    else:
                        frequencies[abstract] = [1, {with_pos: 1}, {with_pos: wp_ex_steps}, {with_pos: wp_ex_states}]
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
                    pairs.append((freq[0], pair, freq[1], freq[2], freq[3]))
            else:
                if freq >= thres:
                    pairs.append((freq, pair))

        pairs.sort(reverse=True)
        top_pairs = pairs[:self.top]
        top_abs = []
        if self.peek_pos:
            for freq, pair, rel_pos_freq, rel_pos_ex_steps, rel_pos_ex_states in top_pairs:
                pair.freq = freq / len(solutions)
                pair.rel_pos_freq = {rel_pos: pfreq / len(solutions) for rel_pos, pfreq in rel_pos_freq.items()}
                pair.rel_pos_ex_steps = rel_pos_ex_steps
                pair.rel_pos_ex_states = rel_pos_ex_states
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
            abstractor = IterAbsPairs(sols, axioms, self.config)
            sols = abstractor.abstracted_sol(2)
            axioms = abstractor.new_axioms
        
        return sols, axioms




if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Find mathematical absractions.")
    parser.add_argument("-t", dest="test", action="store_true", help="Testing")
    parser.add_argument("--file", type=str, help="File to store the abstractions")
    parser.add_argument("--iter", type=int, default=1, help="How many times to iterate pair abstraction process")
    parser.add_argument("--thres", type=float, default=None, help="Threshold frequency for abstractions")
    parser.add_argument("--top", metavar="K", type=int, default=None, help="Choose top K abstractions")
    parser.add_argument("--tree", dest="tree_idx", action="store_true", help="Consider relative positions in expression tree")
    parser.add_argument("--pos", dest="consider_pos", action="store_true", help="Consider relative positions of application")
    parser.add_argument("--peek", dest="peek_pos", action="store_true", help="Take peek at relative positions even when we don't consider them")
    parser.add_argument("-v", dest="verbose", action="store_true", help="Display example axioms")

    args = parser.parse_args()

    if args.tree_idx:
        solutions = util.load_solutions("equations-8k-tree.json")
    else:
        solutions = util.load_solutions("equations-8k.json")
    _, axioms = util.load_axioms("equation_axioms.json")

    if args.test:
        doctest.testmod()
    else:
        compressor = IterAbsPairs(solutions, axioms, vars(args))
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
                        print('\tEx.  ')
                        for j in range(len(abs_ax[i].ex_steps)):
                            print(f"\t\t{abs_ax[i].ex_states[j]}")
                            print(f"\t\t\t{abs_ax[i].ex_steps[j]}")
                        print(f"\t\t{abs_ax[i].ex_states[-1]}")
            else:
                for i in range(len(axioms), len(abs_ax)):
                    print(str(abs_ax[i]))
                    sorted_rel_pos = sorted(((freq, rp) for rp, freq in abs_ax[i].rel_pos_freq.items()), reverse=True)
                    for freq, rp in sorted_rel_pos:
                        print(f"\t{', '.join(map(str, rp))}\n\t\t{freq}")
                        if args.verbose:
                            print('\t\tEx.  ')
                            for j in range(len(abs_ax[i].rel_pos_ex_steps[rp])):
                                print(f"\t\t\t{abs_ax[i].rel_pos_ex_states[rp][j]}")
                                print(f"\t\t\t\t{abs_ax[i].rel_pos_ex_steps[rp][j]}")
                            print(f"\t\t\t{abs_ax[i].rel_pos_ex_states[rp][-1]}")

    # ex_sol = abs_sol[59]
    # util.print_solution(ex_sol)

