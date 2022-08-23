"""
Simple compression algorithm that finds common subsequences of actions and abstracts them.
"""

import sys
import json
import pickle
import argparse
import warnings
import math
import random
from collections import defaultdict
from dataclasses import dataclass
import heapq
import itertools

from datetime import datetime
import doctest

from steps import Step, AbsStep, Solution
from abstractions import Axiom, Abstraction, ABS_TYPES
import abs_util


def log(x):
    ' For entropy calculations '
    return -1000. if x == 0 else math.log(x)


class Compress:
    def __init__(self, solutions, axioms, config):
        self.solutions = solutions

        self.AbsType = ABS_TYPES[config["abs_type"]]
        self.num_ax = len(axioms)  # num of axioms
        self.axioms = axioms  # list of Rule objects (Axiom objects during first cycle)
        self.axiom_index = {self.axioms[k]: k for k in range(self.num_ax)}  # dictionary mapping axiom names to their indices (as in the list self.axioms)
        self.abstractions = None
        self.new_axioms = self.axioms.copy()  # list containing axioms + additional actions as abstractions (called "new axioms")
        self.new_axiom_set = set(self.new_axioms)

        self.frequencies = None
        self.config = config
        self.peek_pos = config.get("peek_pos", False)

        self.max_abs_len = None

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
        i = 0
        while i <= len(solution.actions) - abs_len:
            ax_subseq = solution.actions[i:i+abs_len]
            new_ax = self.AbsType.from_steps(ax_subseq)
            if new_ax in abstractions:
                new_states = solution.states[:i+1] + solution.states[i+abs_len:]
                new_actions = solution.actions[:i] + [AbsStep(ax_subseq, self.AbsType, solution.states[i:i+abs_len+1])] + solution.actions[i+abs_len:]
                solution = Solution(new_states, new_actions)
            i += 1
        return solution
    
    def abstracted_sol(self, abstractions=None, num_new_sols=None):
        """
        Get abstracted solutions from set of abstractions
        Format: same as self.solutions
        (i.e. tuple of Solution objects)
        """
        abstractions = self.abstractions or self.abstract()
        max_len =  max(len(abstraction.rules) for abstraction in abstractions) if self.max_abs_len is None else self.max_abs_len
        
        self.new_axioms += abstractions
        abs_set = set(abstractions)
        self.new_axiom_set |= abs_set

        new_sols = self.solutions.copy() if num_new_sols is None else self.solutions[:num_new_sols]
        for abs_len in range(max_len, 1, -1):
            for i in range(len(new_sols)):
                new_sols[i] = self.abstract_step(new_sols[i], abs_len, abs_set)
                # while True:
                #     res = self.abstract_step(new_sols[i], abs_len, abs_set)
                #     if res is None:
                #         break
                #     else:
                #         new_sols[i] = res
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
        thres = int(math.ceil(len(solutions) * thres))
        graph = self.get_frequencies() >= thres

        if draw:
            print(graph.astype(int))
            abs_util.draw_graph(self.num_ax, graph)

        return CommonPairs.maximal_paths(self.num_ax, graph)


class IterAbsPairs(Compress):
    def __init__(self, solutions, axioms, config):
        super().__init__(solutions, axioms, config)
        self.thres = config.get("thres")
        self.top = config.get("top")
        self.only_flat = config.get("only_flat", False)
        self.max_abs_len = 2

    def get_frequencies(self, factor=1, max_len=2, min_len=2):
        """
        Gets frequencies of (current action, next action) pairs
        Also stores example abstraction for each rel. pos. if --peek
        `factor` is factor to divide no. of occurrences by
        """
        frequencies = defaultdict(int) if not self.peek_pos else defaultdict(lambda: [0, defaultdict(int), {}, {}])
        for i, sol in enumerate(self.solutions):
            for length in range(min_len, 1 + (max_len or len(sol.actions))):
                for j in range(len(sol.actions) - length + 1):
                    if self.only_flat and any(len(sol.actions[k]) != 1 for k in range(j, j+length)):
                        continue
                    abstract = self.AbsType.from_steps(sol.actions[j:j+length], ex_states=sol.states[j:j+length+1])
                    if not self.peek_pos:
                        frequencies[abstract] += 1
                    else:
                        frequencies[abstract][0] += 1
                        wp_abs = AxSeqTreeRelPos.from_steps(sol.actions[j:j+length], ex_states=sol.states[j:j+length+1])
                        frequencies[abstract][1][wp_abs.rel_pos] += 1
                        frequencies[abstract][2][wp_abs.rel_pos] = wp_abs.ex_steps
                        frequencies[abstract][3][wp_abs.rel_pos] = wp_abs.ex_states
        if not self.peek_pos:
            for abstract in frequencies:
                frequencies[abstract] /= factor
                abstract.freq = frequencies[abstract]
        else:
            for abstract, freq_info in frequencies.items():
                freq_info[0] /= factor
                for rel_pos in freq_info[1]:
                    freq_info[1][rel_pos] /= factor
                abstract.freq, abstract.rel_pos_freq, abstract.rel_pos_ex_steps, abstract.rel_pos_ex_states = freq_info
                frequencies[abstract] = freq_info[0]
        self.frequencies = frequencies
        return frequencies

    def abstract(self):
        """
        Finds common length-2 subsequences (current action, next action)
        that appear with frequency >= thres in dataset of solutions
        """
        thres = (self.num_ax**(-0.75) if self.top is None else 0) if self.thres is None else self.thres  # -0.75 is just an arbitrary exponent
        frequencies = self.frequencies or self.get_frequencies(len(self.solutions))
        pairs = list(filter(lambda x: x.freq >= thres, frequencies.keys()))
        pairs.sort(reverse=True, key=lambda x: x.freq)
        top_pairs = pairs[:self.top]
        self.abstractions = top_pairs
        return top_pairs

    def iter_abstract(self, K, get_new_sols=False, num_new_sols=None):
        """
        Abstract common (cur, next) pairs iteratively K times
        """
        sols = self.solutions
        axioms = self.axioms
        for i in range(K):
            abstractor = self.__class__(sols, axioms, self.config)
            abstractions = abstractor.abstract()
            if not abstractions:
                if get_new_sols:
                    return (sols, axioms) if num_new_sols is None else (sols[:num_new_sols], axioms)
                return axioms
            if i == K - 1:
                if get_new_sols:
                    sols = abstractor.abstracted_sol(num_new_sols=num_new_sols)
                    return sols, abstractor.new_axioms
                return axioms + abstractions
            sols = abstractor.abstracted_sol()
            axioms = abstractor.new_axioms


class IAPHeuristic(IterAbsPairs):
    def get_frequencies(self, factor=1):
        """
        Gets heuristic scores of (current action, next action) pairs
        Also stores example abstraction for each rel. pos. if --peek
        """
        frequencies = defaultdict(int) if not self.peek_pos else defaultdict(lambda: [0, defaultdict(int), {}, {}])
        for i, sol in enumerate(self.solutions):
            abstracts = []
            for j in range(len(sol.actions)-1):
                abstract = self.AbsType.from_steps(sol.actions[j:j+2], ex_states=sol.states[j:j+3])
                abstracts.append(abstract)
                if len(sol.actions[j]) > 1 or len(sol.actions[j+1]) > 1:
                    abstract_flat = self.AbsType.from_steps(sol.actions[j].steps + sol.actions[j+1].steps, ex_states=sol.actions[j].ex_states[:-1] + sol.actions[j+1].ex_states)
                    abstracts.append(abstract_flat)

            scores = [len(abstract) + abstract.height for abstract in abstracts]

            if not self.peek_pos or self.consider_pos or self.tree_idx:
                for abstract, score in zip(abstracts, scores):
                    frequencies[abstract] += score
            else:
                wp_abstracts = []
                for j in range(len(sol.actions)-1):
                    wp_abs = AxSeqTreeRelPos.from_steps(sol.actions[j:j+2], ex_states=sol.states[j:j+3])
                    wp_abstracts.append(wp_abs)
                    wp_abs_flat = AxSeqTreeRelPos.from_steps(sol.actions[j].steps + sol.actions[j+1].steps, ex_states=sol.actions[j].ex_states[:-1] + sol.actions[j+1].ex_states)
                    wp_abstracts.append(wp_abs_flat)
                for wp_abs, abstract, score in zip(wp_abstracts, abstracts, scores):
                    with_pos, wp_ex_steps, wp_ex_states = wp_abs.rel_pos, wp_abs.ex_steps, wp_abs.ex_states
                    frequencies[abstract][0] += score
                    frequencies[abstract][1][with_pos] += score
                    frequencies[abstract][2][with_pos] = wp_ex_steps
                    frequencies[abstract][3][with_pos] = wp_ex_states
        if not self.peek_pos:
            for abstract in frequencies:
                frequencies[abstract] /= factor
                abstract.freq = frequencies[abstract]
        else:
            for abstract, freq_info in frequencies.items():
                freq_info[0] /= factor
                for rel_pos in freq_info[1]:
                    freq_info[1][rel_pos] /= factor
                abstract.freq, abstract.rel_pos_freq, abstract.rel_pos_ex_steps, abstract.rel_pos_ex_states = freq_info
                frequencies[abstract] = freq_info[0]
        self.frequencies = frequencies
        return frequencies


@dataclass
class AbsHeapElt:
    abstraction: Abstraction

    def __lt__(self, other):
        return self.abstraction.score > other.abstraction.score


class IAPLogN(IterAbsPairs):
    def __init__(self, solutions, axioms, config):
        super().__init__(solutions, axioms, config)
        self.max_abs_len = config.get("max_abs_len")
        self.include_eos = config.get("include_eos", False)
        # assert self.top is None and self.thres is None  # automatically determine no. abs.

    def abstract(self):
        """
        Uses log factor in uniform distribution probabilistic model to determine no. of abs.
        Only chooses one abstraction; use `iter_abstract` to get multiple
        """
        frequencies = self.frequencies or self.get_frequencies(len(self.solutions), self.max_abs_len)
        all_frequencies = self.frequencies or self.get_frequencies(len(self.solutions), 2*self.max_abs_len-1, self.max_abs_len+1)
        all_frequencies |= frequencies

        for abstract in all_frequencies:
            abstract.score = abstract.freq * (len(abstract) - 1)
        abs_heap = [AbsHeapElt(abstraction) for abstraction in frequencies]
        heapq.heapify(abs_heap)

        num_abs_ax = len(self.axioms) + self.include_eos
        avg_length = sum(len(sol.actions) for sol in self.solutions) / len(self.solutions) + self.include_eos
        top_abs = []
        while True:
            top = heapq.heappop(abs_heap).abstraction
            increment = top.score * log(num_abs_ax + 1) - log(1 + 1/num_abs_ax) * avg_length
            print(increment)
            if increment < 0:
                break
            top_abs.append(top)
            num_abs_ax += 1
            avg_length -= top.score
            break
            # for l in range(-self.max_abs_len+1, len(top)):
            #     for r in range(max(1, l+2), l+self.max_abs_len+1):
            #         lol
        self.abstractions = top_abs
        return top_abs


class IAPEntropy(IterAbsPairs):
    """
    Currently doesn't bias towards higher-frequency abstractions
    """
    def __init__(self, solutions, axioms, config):
        super().__init__(solutions, axioms, config)
        self.ax_freqs = None
        self.max_abs_len = config.get("max_abs_len")
        assert self.top is None and self.thres is None  # Use entropy to determine optimal no. of abs.
        assert not self.peek_pos  # not implemented

    def get_ax_freqs(self, factor=1):
        ax_freqs = defaultdict(int)
        for sol in solutions:
            for action in sol.actions:
                ax_freqs[action.rule] += 1
        if factor != 1:
            for ax in ax_freqs:
                ax_freqs[ax] /= factor
        self.ax_freqs = ax_freqs
        return ax_freqs

    def abstract(self):
        """
        Finds abstractions to decrease entropy
        """
        avg_length = sum(len(sol.states) for sol in self.solutions) / len(self.solutions)  # includes <eos>
        frequencies = self.frequencies or self.get_frequencies(len(self.solutions), self.max_abs_len)
        ax_freqs = self.ax_freqs or self.get_ax_freqs(len(self.solutions))
        # H = -sum(freq * np.log(freq/avg_length) for freq in ax_freqs.values()) + np.log(avg_length)
        top_pairs = []
        for pair, freq in frequencies.items():
            f_ax = [ax_freqs[ax] for ax in pair.rules]
            new_length = avg_length - freq * (len(pair) - 1)
            prob = freq / new_length
            p_ax = list(map(lambda x: x / new_length, f_ax))
            pair.score = freq*log(prob) + sum((fi-freq)*log(pi-prob) for fi, pi in zip(f_ax, p_ax)) \
                - sum(fi*log(pi) for fi, pi in zip(f_ax, p_ax)) \
                + log(avg_length / new_length)
            if pair.score > 0:
                top_pairs.append(pair)
        top_pairs.sort(reverse=True, key=lambda x: x.score)
        self.abstractions = top_pairs
        return top_pairs


class IAPTriePrune(IterAbsPairs):
    def __init__(self, solutions, axioms, config):
        super().__init__(solutions, axioms, config)
        self.max_abs_len = None

    def abstract(self):
        """
        Build trie from common axiom pairs and longer abstractions formed from chaining together pairs
        Take abstractions with high frequency
        Remove abstractions with significantly lower frequency than subabstractions
        """
        top_pairs = set(super().abstract())  # set of Abstraction objects
        # abstract_trie = abs_util.Trie()
        # for pair in top_pairs:
        #     abstract_trie.add([(None, pair.rules[0]), (pair.rel_pos[0], pair.rules[1])], int(pair.freq*len(self.solutions)))
        # print(abstract_trie)
        # print('\n')
        abstract_trie = abs_util.Trie()
        for pair in top_pairs:
            abstract_trie.add([(None, pair.rules[0]), (pair.rel_pos[0], pair.rules[1])], 0, (pair.ex_steps, pair.ex_states))
        for sol in self.solutions:
            i = 0
            while i < len(sol.actions) - 1:
                cur_node = abstract_trie.children.get((None, sol.actions[i].rule))
                if cur_node is None:
                    i += 1
                    continue
                j = i
                while j < len(sol.actions) - 1:
                    pair = self.AbsType.from_steps(sol.actions[j:j+2])
                    if pair in top_pairs:
                        next_abs_elt = (pair.rel_pos[0], pair.rules[1])
                        if next_abs_elt in cur_node.children:
                            cur_node = cur_node.children[next_abs_elt]
                            cur_node.value += 1
                        else:
                            cur_node = cur_node.add([next_abs_elt], 1, (sol.actions[i:j+2], sol.states[i:j+3]))
                        j += 1
                    else:
                        break
                i = j + 1
        # print(abstract_trie)
        def dfs_pruner(trie, depth=0):
            if not trie.is_term:
                for sub_trie in trie.children.values():
                    dfs_pruner(sub_trie, depth+1)
            else:
                keys = list(trie.children.keys())
                for key in keys:
                    sub_trie = trie.children[key]
                    if sub_trie.value / trie.value <= (depth - 1) / depth:
                        trie.children.pop(key)
                    else:
                        dfs_pruner(sub_trie, depth+1)
        dfs_pruner(abstract_trie)
        # print(abstract_trie)
        def dfs_make_abs(trie, store_abs, keys_so_far=[]):
            if not trie.children:
                abstraction = self.AbsType.from_abs_elt(keys_so_far, ex_states=trie.comment[1])
                abstraction.ex_steps = trie.comment[0]
                abstraction.freq = trie.value / len(self.solutions)
                store_abs.append(abstraction)
            else:
                for key, sub_trie in trie.children.items():
                    keys_so_far.append(key)
                    dfs_make_abs(sub_trie, store_abs, keys_so_far)
                    keys_so_far.pop()
        abstractions = []
        dfs_make_abs(abstract_trie, abstractions)
        abstractions.sort(key=lambda x: x.freq, reverse=True)
        # print(abstractions)
        self.abstractions = abstractions
        return abstractions


class AbsDTrieHeapElt:
    def __init__(self, abstraction: abs_util.DoubleTrie, num_sols: int):
        self.abstraction = abstraction
        self.score = self.abstraction.value * (self.abstraction.depth - 1) / num_sols
        self.removed = False

    def __lt__(self, other):
        return self.score > other.score


class IAPDTrieLogN(IAPLogN):
    def get_frequencies(self, factor=1, max_len=None):
        frequencies = abs_util.DoubleTrie(accum=True)
        for sol in self.solutions:
            if len(sol.actions) > 1:
                abstraction = self.AbsType.from_steps(sol.actions)
                frequencies.add(abstraction.rules, 1, abstraction.__dict__.get("rel_pos"), max_length=max_len)
        if factor != 1:
            def dfs(node, not_root=True):
                if not_root:
                    node.value /= factor
                for child in node.append_children.values():
                    dfs(child)
            dfs(frequencies, False)
        self.frequencies = frequencies
        return frequencies

    def abstract(self):
        frequencies = self.frequencies or self.get_frequencies()

        def dfs(node, depth=0):
            if depth >= 2:
                yield node
            if self.max_abs_len is None or depth < self.max_abs_len:
                for child in node.append_children.values():
                    yield from dfs(child, depth+1)
        abs_heap = [AbsDTrieHeapElt(ab, len(self.solutions)) for ab in dfs(frequencies)]
        heapq.heapify(abs_heap)
        abs_heap_dict = {abs_heap_elt.abstraction: abs_heap_elt for abs_heap_elt in abs_heap}

        def pop_heap():
            while (top_heap_elt := heapq.heappop(abs_heap)).removed:
                continue
            top_node = top_heap_elt.abstraction
            del abs_heap_dict[top_node]
            return top_node, top_heap_elt.score

        def update(node):
            if node in abs_heap_dict:
                abs_heap_dict[node].removed = True
                new_heap_elt = AbsDTrieHeapElt(node, len(self.solutions))
                heapq.heappush(abs_heap, new_heap_elt)
                abs_heap_dict[node] = new_heap_elt

        # def dfs_overlap(node, abs_len, prepend: bool):  # l > L, r >= R; l <= L, r < R
        #     cur_node = node
        #     for _ in range(abs_len-1):
        #         cur_node = cur_node.append_parent if prepend else cur_node.prepend_parent
        #         cur_node.value -= node.value
        #         update(cur_node)
        #     for next_node in (node.prepend_children if prepend else node.append_children).values():
        #         dfs_overlap(next_node, abs_len, prepend)

        def dfs_overlap(node, super_node, prepend: bool):  # l > L, r >= R; l <= L, r < R
            node.value -= super_node.value
            update(node)
            children = node.prepend_children if prepend else node.append_children
            super_children = super_node.prepend_children if prepend else super_node.append_children
            for next_key, next_node in children.items():
                if next_node.value and next_key in super_children:
                    dfs_overlap(next_node, super_children[next_key], prepend)

        def dfs_super_helper(node):
            node.value = 0
            update(node)
            for next_node in node.append_children.values():
                if next_node.value:
                    dfs_super_helper(next_node)

        def dfs_super(node):  # l <= L, r >= R
            dfs_super_helper(node)
            for next_node in node.prepend_children.values():
                if next_node.value:
                    dfs_super(next_node)

        num_abs_ax = len(self.axioms) + self.include_eos
        avg_length = sum(len(sol.actions) for sol in self.solutions) / len(self.solutions) + self.include_eos
        top_abs = []
        print("ABS SCORE INCREMENTS:")
        for count in itertools.count() if self.top is None else range(self.top):
            # with open(f"debug/debug_{count}.txt", "w") as f:
            #     f.write(str(frequencies))
            # print(max(x.score for x in abs_heap if not x.removed))
            # print(max(x.value * (x.depth-1) for x in abs_heap_dict))
            top, score = pop_heap()
            occurs = top.value
            # print(score)
            increment = score * log(num_abs_ax + 1) - log(1 + 1/num_abs_ax) * avg_length
            print(increment)
            if self.top is None and increment < 0:
                break
            top_abs.append((top, occurs / len(self.solutions), score))
            num_abs_ax += 1
            # print(avg_length)
            avg_length -= score
            # print(avg_length)
            # l > L, r >= R; l <= L, r < R
            # breakpoint()
            for prepend in [False, True]:
                cur_node = top
                for _ in range(top.depth-1):
                    cur_node = cur_node.append_parent if prepend else cur_node.prepend_parent
                    dfs_overlap(cur_node, top, prepend)
            # l <= L, r >= R
            dfs_super(top)
            # l > L, r < R
            node = top
            for i in range(1, top.depth-1):
                node = node.prepend_parent
                cur_node = node
                for _ in range(1, top.depth-i):
                    cur_node = cur_node.append_parent
                    cur_node.value -= occurs
                    update(cur_node)

        def get_shifted_abs_elts(node):
            cur_node = node
            for _ in range(node.depth):
                yield cur_node.prepend_key
                cur_node = cur_node.prepend_parent
        self.abstractions = [self.AbsType.from_shifted_abs_elt(get_shifted_abs_elts(node)) for node, _, _ in top_abs]
        for ab, (_, freq, score) in zip(self.abstractions, top_abs):
            ab.freq = freq
            ab.score = score
        return self.abstractions


COMPRESSORS = {"pair_graph": CommonPairs, "iap": IterAbsPairs, "iap_heur": IAPHeuristic, "iap_ent": IAPEntropy,
               "iap_logn": IAPLogN, "iap_trie": IAPTriePrune, "iap_dtrie": IAPDTrieLogN}


def debug():
    solutions = abs_util.load_solutions("equations-80k-relative.json")
    solutions = [Solution.from_dict(sol) for sol in solutions[:1000]]
    _, axioms = abs_util.load_axioms("equation_axioms.json")
    compressor = IAPTriePrune(solutions, axioms, {"top": 8, "abs_type": "tree_rel_pos"})
    compressor.abstract()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Find mathematical absractions.")
    parser.add_argument("-t", dest="test", action="store_true", help="Testing")
    parser.add_argument("--config", dest="config_file", type=str, help="Configuration file (can override other options)")
    parser.add_argument("--sol-data", type=str, help="Path to data of solutions from which abstractions are found")
    parser.add_argument("--file", type=str, help="File to store the abstractions")
    parser.add_argument("--sol-file", type=str, help="File to store the abstracted solutions")
    parser.add_argument("--use", dest="num_use", type=int, default=None, help="How many solutions to use (default: all)")
    parser.add_argument("--store", dest="num_store", type=int, default=None, help="How many abstracted solutions to store (default: all)")
    parser.add_argument("--num-ex-sol", dest="num_ex_sol", type=int, default=0, help="Number of example solutions to display")
    parser.add_argument("-s", dest="small", action="store_true", help="Whether to use small dataset")
    parser.add_argument("--iter", type=int, default=1, help="How many times to iterate pair abstraction process")
    parser.add_argument("--thres", type=float, default=None, help="Threshold frequency for abstractions")
    parser.add_argument("--top", metavar="K", type=int, default=None, help="Choose top K abstractions")
    parser.add_argument("--abs-type", dest="abs_type", default="tree_rel_pos", choices=["ax_seq", "dfs_idx_rel_pos", "tree_rel_pos"], help="Type of abstraction")
    parser.add_argument("--compressor", default="iap_heur", choices=["pair_graph", "iap", "iap_heur", "iap_ent", "iap_logn", "iap_trie", "iap_dtrie"], help="Type of algorithm for discovering abstractions")
    parser.add_argument("--peek", dest="peek_pos", action="store_true", help="Take peek at relative positions (with abs. type tree_rel_pos) even when we don't consider them")
    parser.add_argument("-v", dest="verbose", action="store_true", help="Display example axioms")
    parser.add_argument("--debug", action="store_true", help="Debug")

    args = parser.parse_args()
    if args.config_file is not None:
        with open(args.config_file, 'r') as f:
            args.__dict__.update(json.load(f))

    if args.debug:
        debug()
        sys.exit()

    if args.small:
        num_use = args.num_use or 8000
        num_store = args.num_store or 8000
    else:
        num_use = args.num_use or 80000
        num_store = args.num_store or 80000

    if args.sol_data is None:
        if args.abs_type == "tree_rel_pos":
            solutions = abs_util.load_solutions("equations-80k-relative.json")
        else:
            if args.small:
                solutions = abs_util.load_solutions("equations-8k.json")
            else:
                solutions = abs_util.load_solutions("equations-80k.json")
    elif isinstance(args.sol_data, str):
        with open(args.sol_data, 'r') as f:
            solutions = abs_util.load_solutions(args.sol_data)
    else:
        solutions = args.sol_data
    _, axioms = abs_util.load_axioms("equation_axioms.json")
    axioms = [Axiom(ax_name) for ax_name in axioms]

    if args.test:
        doctest.testmod()
    else:
        used_sols = solutions[:num_use] if isinstance(num_use, int) else [solutions[i] for i in num_use]
        solutions = [Solution.from_dict(sol, AbsType=ABS_TYPES[args.abs_type]) for sol in used_sols]
        start_time = datetime.now()
        compressor = COMPRESSORS[args.compressor](solutions, axioms, vars(args))
        if args.sol_file is not None or args.num_ex_sol:
            sols, abs_ax = compressor.iter_abstract(args.iter, True, num_store)
            print("TOTAL TIME:", datetime.now() - start_time)
            if args.sol_file is not None:
                with open(args.sol_file, "wb") as f:
                    pickle.dump(sols, f)
            if args.num_ex_sol is not None:
                for i, ex_sol in enumerate(random.sample(sols, args.num_ex_sol)):
                    print(f"EXAMPLE SOLUTION {i+1}")
                    print(ex_sol)
                    print('\n')
        else:
            abs_ax = compressor.iter_abstract(args.iter)
            print("TOTAL TIME:", datetime.now() - start_time)
        if args.file is not None:
            if args.file[-5:] == ".json":
                abs_ax_str = list(map(str, abs_ax))
                with open(args.file, "w") as f:
                    json.dump({"num": len(abs_ax_str), "axioms": abs_ax_str}, f)
            elif args.file[-4:] == ".pkl":
                with open(args.file, "wb") as f:
                    pickle.dump(abs_ax, f)
        print("NUM NEW ABS:", len(abs_ax) - len(axioms))
        if args.abs_type in ["tree_rel_pos", "dfs_idx_rel_pos"] or not args.peek_pos:
            for i in range(len(axioms), len(abs_ax)):
                print(f"{str(abs_ax[i])}\n\t{abs_ax[i].score or abs_ax[i].freq}")
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
    # abs_util.print_solution(ex_sol)

