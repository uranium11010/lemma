"""
Simple compression algorithm that finds common subsequences of actions and abstracts them.
"""

import json
import numpy as np
import matplotlib.pyplot as plt
import warnings

import util


def get_frequencies(solutions, num_ax, axioms, get_ax_name):
    """
    Gets frequencies of (current action, next action) pairs
    """
    frequencies = np.zeros((num_ax, num_ax), dtype=int)
    axiom_index = {axioms[k]: k for k in range(num_ax)}
    for i in range(len(solutions)):
        sol = solutions[i]["solution"]
        for step in range(1, len(sol)-1):
            action_cur = axiom_index[get_ax_name(sol[step]["action"])]
            action_next = axiom_index[get_ax_name(sol[step+1]["action"])]
            frequencies[action_cur, action_next] += 1
    
    return frequencies


def dfs(N, graph, cur, paths, visited, cur_paths):
    """
    Finds all paths in graph starting at 'cur' node
    Adds them to 'paths' (or augments existing paths)
    Indices of paths in 'paths' that 'cur' node belongs to are in 'cur_paths'
    Nodes in paths to that led to 'cur' node are in 'visited'
    ATTENTION: NOT YET OPTIMIZED FOR WHEN MANY PATHS GO TO SAME NODE (i.e. dfs would be repeatedly called on that node)
    """
    copied_cur_paths = [paths[path_idx].copy() for path_idx in cur_paths]
    first_next = True
    for next in range(N):
        if graph[cur, next]:
            if first_next:
                for path_idx in cur_paths:
                    paths[path_idx].append(next)
                next_paths = cur_paths
                first_next = False
            else:
                next_paths = []
                for cur_path in copied_cur_paths:
                    paths.append(cur_path + [next])
                    next_paths.append(len(paths)-1)
            
            if next in visited:
                warnings.warn("Cool fact--the graph has cycles :)")
                continue
            
            new_visited = visited.copy()
            new_visited.add(next)
            dfs(N, graph, next, paths, new_visited, next_paths)


def maximal_paths(N, graph):
    """
    Helper for common_subseq(..)
    Finds maximal paths in directed graph given by adjacency matrix 'graph'; N = # nodes
    ATTENTION: NOT 'MAXIMAL' IN THE REVERSE DIRECTION (SO IF [2, 5, 3, 5] IS DETECTED, [5, 3, 5] ALSO WOULD BE),
    HENCE THERE ARE MANY REDUNDANCIES
    """
    paths = []
    for node in range(N):
        paths.append([node])
        dfs(N, graph, node, paths, {node}, [len(paths)-1])
    
    return paths


def common_subseq(solutions, num_ax, axioms, get_ax_name, thres=None):
    """
    Finds common subsequences among solutions where any (current action, next action)
    pair within subsequence appears a fruency >= thres in dataset of solutions
    """
    thres = num_ax**(-0.75) if thres is None else thres # -0.75 is just an arbitrary number between -1 and 0 that I chose
    thres = int(np.ceil(len(solutions) * thres))
    graph = get_frequencies(solutions, num_ax, axioms, get_ax_name) >= thres

    print(graph.astype(int))
    util.draw_graph(num_ax, graph)
    return maximal_paths(num_ax, graph)


def get_ax_name(ax_full):
    """
    Get name of axiom from a string 'ax_full' specifying both axiom and what it's applied to
    """
    return ax_full.split()[0]


if __name__ == "__main__":
    solutions = util.load_solutions("equations-8k.json")
    num_ax, axioms = util.load_axioms("equation_axioms.json")

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

    abstractions = common_subseq(solutions, num_ax, axioms, get_ax_name)
    print(abstractions)

