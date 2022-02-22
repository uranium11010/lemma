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
    

    def common_subseq(self):
        raise NotImplementedError

    
    @staticmethod
    def abstract_step(states, actions, abs_len, abstractions):
        """
        In solution, abstract out the first length-'abs_len' subsequence that is an abstraction
        'actions' is tuple of integers denoting axioms in the solution
        'states' is a list of states in the solution
        """
        for i in range(len(actions)-abs_len+1):
            if actions[i:i+abs_len] in abstractions:
                new_actions = actions[:i] + (-1,) + actions[i+abs_len:]
                new_states = states[:i+1] + states[i+abs_len:]
                return new_states, new_actions

    
    def abstracted_sol(self, max_len, abstractions=None):
        """
        Get abstracted solutions from set of abstractions
        """
        if abstractions is None:
            abstractions = self.common_subseq()
        
        new_sols = [([self.solutions[i]["solution"][step]["state"] for step in range(len(self.solutions[i]["solution"]))],
                    tuple(self.axiom_index[self.get_ax_name(self.solutions[i]["solution"][step]["action"])] for step in range(1, len(self.solutions[i]["solution"]))))
                             for i in range(len(self.solutions))]
        for i in range(len(new_sols)):
            new_sol = new_sols[i]
            # print("BEGIN", new_sol[1])
            for abs_len in range(max_len, 1, -1):
                while True:
                    res = CommonPairs.abstract_step(*new_sol, abs_len, abstractions)
                    if res is None:
                        break
                    else:
                        new_sol = res
                        # print("ABS_LEN", abs_len, new_sol[1])
            
            new_sols[i] = new_sol
        
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


    def common_subseq(self):
        """
        Finds common subsequences among solutions where any (current action, next action)
        pair within subsequence appears with frequency >= thres in dataset of solutions
        """
        thres = self.num_ax**(-0.75) if self.thres is None else self.thres # -0.75 is just an arbitrary number between -1 and 0 that I chose
        thres = int(np.ceil(len(solutions) * thres))
        graph = self.get_frequencies() >= thres

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
            # EDIT abstracted_sol() SUCH THAT IT RETURNS SOLUTIONS IN THE SAME FORMAT AS BEFORE
            sols = abstractor.abstracted_sol(2, abstractions)
            axioms = axioms + [k+len(axioms) for k in range(len(abstractions))]
        
        return sols, axioms




def get_ax_name(ax_full):
    """
    Get name of axiom from a string 'ax_full' specifying both axiom and what it's applied to
    """
    return ax_full.split()[0]


if __name__ == "__main__":
    solutions = util.load_solutions("equations-8k.json")
    _, axioms = util.load_axioms("equation_axioms.json")

    # freq = get_frequencies(solutions, num_ax, axioms, get_ax_name)
    # print(freq)
    # common_subseq(solutions, num_ax, axioms, get_ax_name)

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

    compressor = CommonPairs(solutions, axioms, get_ax_name)
    abstractions = compressor.common_subseq()
    # print(abstractions)
    abs_sol = compressor.abstracted_sol(5, abstractions=abstractions)
    ex_sol = abs_sol[59]
    print("State 0:", ex_sol[0][0])
    for i in range(1, len(ex_sol[0])):
        ax_idx = ex_sol[1][i-1]
        ax = axioms[ax_idx] if ax_idx >= 0 else "ABSTRACTION"
        print("Action {}:".format(i), ax)
        print("State {}:".format(i), ex_sol[0][i])

