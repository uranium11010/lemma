"""
Simple compression algorithm that finds common subsequences of actions and abstracts them.
"""

import json
import numpy as np
import matplotlib.pyplot as plt
import warnings

import util


class Compress(object):
    def __init__(self, solutions, axioms, get_ax_name):
        self.solutions = solutions
        self.num_ax = len(axioms)
        self.axioms = axioms
        self.get_ax_name = get_ax_name
        self.axiom_index = {self.axioms[k]: k for k in range(self.num_ax)}
        self.new_axioms = self.axioms.copy()
        self.new_axiom_set = set(self.new_axioms)
        self.new_axiom_index = self.axiom_index.copy()
    

    def common_subseq(self):
        raise NotImplementedError


    def get_axiom_tuple(self, solution):
        """
        Get tuple of integers corresponding to axioms in solution
        solution: format in self.solutions[i]["solution"] (i.e. list of state-action pairs as dictionaries)
        """
        return tuple(self.axiom_index.get(self.get_ax_name(solution[i]["action"])) for i in range(1, len(solution)))
    

    def abstract_step(self, solution, abs_len, abstractions):
        """
        In solutions, abstract out the first length-'abs_len' subsequence that is an abstraction
        solution: format in self.solutions[i]["solution"] (i.e. list of state-action pairs as dictionaries)
        """
        axiom_list = self.get_axiom_tuple(solution)
        for i in range(len(solution)-abs_len):
            if axiom_list[i:i+abs_len] in abstractions:
                new_ax = "["
                for j in range(i, i+abs_len-1):
                    new_ax += self.axioms[axiom_list[j]] + "-"
                new_ax += self.axioms[axiom_list[i+abs_len-1]] + "]"
                if new_ax not in self.new_axiom_set:
                    self.new_axiom_index[new_ax] = len(self.new_axioms)
                    self.new_axioms.append(new_ax)
                    self.new_axiom_set.add(new_ax)

                # MAYBE ALSO ALLOW PUTTING TERMS INTO INFORMATION

                first_steps = solution[:i+1]
                abs_step = {"state": solution[i+abs_len]["state"], "action": new_ax}
                last_steps = solution[i+abs_len+1:]
                
                return first_steps + [abs_step] + last_steps

    
    def abstracted_sol(self, max_len, abstractions=None):
        """
        Get abstracted solutions from set of abstractions
        Format: same as self.solutions
        (i.e. {"problem": problem, "solution": [{"state": state, "action": "assumption"},
                                                {"state": state, "action": "axiom_name, term"}, ...]}
        """
        if abstractions is None:
            abstractions = self.common_subseq()
        
        new_sols = self.solutions.copy()
        for abs_len in range(max_len, 1, -1):
            for i in range(len(new_sols)):
                # print("BEGIN", new_sol[1])
                while True:
                    res = self.abstract_step(new_sols[i]["solution"], abs_len, abstractions)
                    if res is None:
                        break
                    else:
                        new_sols[i]["solution"] = res
                        # print("ABS_LEN", abs_len, new_sol[1])
        
        return new_sols




class CommonPairs(Compress):
    """
    Finds common (cur, next) action pairs among solutions and constructs corresponding
    digraph with these pairs as edges.
    Uses paths of this digraph as abstractions.
    """
    def __init__(self, solutions, axioms, get_ax_name, thres=None):
        super().__init__(solutions, axioms, get_ax_name)
        self.thres = thres

    def get_frequencies(self):
        """
        Gets frequencies of (current action, next action) pairs
        """
        frequencies = np.zeros((self.num_ax, self.num_ax), dtype=int)
        for i in range(len(self.solutions)):
            sol = self.solutions[i]["solution"]
            for step in range(1, len(sol)-1):
                action_cur = self.axiom_index[get_ax_name(sol[step]["action"])]
                action_next = self.axiom_index[get_ax_name(sol[step+1]["action"])]
                frequencies[action_cur, action_next] += 1
        
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


    def common_subseq(self, draw=False):
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
    def __init__(self, solutions, axioms, get_ax_name, thres=None):
        super().__init__(solutions, axioms, get_ax_name)
        self.thres = thres


    def get_frequencies(self):
        """
        Gets frequencies of (current action, next action) pairs
        """
        frequencies = np.zeros((self.num_ax, self.num_ax), dtype=int)
        for i in range(len(self.solutions)):
            sol = self.solutions[i]["solution"]
            for step in range(1, len(sol)-1):
                action_cur = self.axiom_index[get_ax_name(sol[step]["action"])]
                action_next = self.axiom_index[get_ax_name(sol[step+1]["action"])]
                frequencies[action_cur, action_next] += 1
        
        return frequencies

    
    def common_subseq(self):
        """
        Finds common length-2 subsequences (current action, next action)
        that appear with frequency >= thres in dataset of solutions
        """
        thres = self.num_ax**(-0.75) if self.thres is None else self.thres # -0.75 is just an arbitrary number between -1 and 0 that I chose
        thres = int(np.ceil(len(solutions) * thres))
        graph = self.get_frequencies() >= thres

        pairs = set()
        for i in range(self.num_ax):
            for j in range(self.num_ax):
                if graph[i,j]:
                    pairs.add((i, j))

        return pairs
    

    def iter_abstract(self, K):
        """
        Abstract common (cur, next) pairs iteratively K times
        """
        sols = self.solutions
        axioms = self.axioms
        for _ in range(K):
            abstractor = IterAbsPairs(sols, axioms, self.get_ax_name, self.thres)
            abstractions = abstractor.common_subseq()
            sols = abstractor.abstracted_sol(2, abstractions)
            axioms = abstractor.new_axioms
        
        return sols, axioms




def get_ax_name(ax_full):
    """
    Get name of axiom from a string 'ax_full' specifying both axiom and what it's applied to
    """
    return ax_full.split()[0]


if __name__ == "__main__":
    solutions = util.load_solutions("equations-8k.json")
    _, axioms = util.load_axioms("equation_axioms.json")

    # TEST RANDOM THINGS
    # freq = get_frequencies(solutions, num_ax, axioms, get_ax_name)
    # print(freq)
    # common_subseq(solutions, num_ax, axioms, get_ax_name)
    # compressor = CommonPairs(solutions, axioms, get_ax_name)
    # ex_sol = compressor.solutions[0]
    # util.print_solution(ex_sol)
    # print(compressor.get_axiom_list(ex_sol["solution"]))

    # TEST DFS AND maximal_paths(..)
    # graph = np.array(
    #     [[0, 0, 0, 1, 0, 0],
    #     [0, 0, 0, 0, 0, 0],
    #     [0, 1, 0, 0, 1, 0],
    #     [0, 0, 1, 0, 0, 0],
    #     [0, 1, 0, 0, 0, 0],
    #     [0, 0, 0, 0, 0, 1]]
    # )
    # paths = [[0]]
    # dfs(5, graph, 0, paths, {0}, [0])
    # print(paths)
    # print(maximal_paths(6, graph))

    # TEST CommonPairs
    # compressor = CommonPairs(solutions, axioms, get_ax_name)
    # abstractions = compressor.common_subseq()
    # # print(abstractions)
    # abs_sol = compressor.abstracted_sol(5, abstractions=abstractions)
    # ex_sol = abs_sol[59]
    # util.print_solution(ex_sol)

    # TEST IterAbsPairs
    compressor = IterAbsPairs(solutions, axioms, get_ax_name)
    abs_sol, abs_ax = compressor.iter_abstract(5)
    print(abs_ax)
    ex_sol = abs_sol[59]
    util.print_solution(ex_sol)

