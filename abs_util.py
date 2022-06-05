"""
Provides tools for dealing with ConPoLe solutions
"""

import json
import numpy as np
import matplotlib.pyplot as plt

from steps import *

import doctest


def load_solutions(f_name):
    with open(f_name) as sol_f:
        solutions = json.load(sol_f)
    return solutions


def load_axioms(f_name):
    with open(f_name) as ax_f:
        axiom_dict = json.load(ax_f)
        num_ax = axiom_dict["num"]
        axioms = axiom_dict["axioms"]
    return num_ax, axioms


def print_solution(sol):
    """
    Prints a solution 'sol' given as a dictionary
    """
    print("PROBLEM\t", sol["problem"])
    print("SOLUTION")
    for k in range(len(sol["solution"])):
        step = sol["solution"][k]
        print("Action {}:\t".format(k), step["action"])
        print("State {}:\t".format(k), step["state"])


def draw_graph(N, matrix):
    """
    Draws directed graph from adjacency matrix
    """
    plt.axis("off")
    points = []
    for i in range(N):
        points.append((-np.sin(2*np.pi*i/N), np.cos(2*np.pi*i/N)))
        plt.scatter(points[-1][0], points[-1][1], c='C0')
        plt.annotate(str(i), points[-1])

    k = 0
    for i in range(N):
        for j in range(N):
            if matrix[i,j]:
                x1, y1 = points[i]
                x2, y2 = points[j]
                xm, ym = (x1+x2)/2, (y1+y2)/2
                plt.arrow(x1, y1, xm-x1, ym-y1, color="C{}".format(k%10), head_width=0.05, head_length=0.075)
                plt.plot([xm, x2], [ym, y2], color="C{}".format(k%10))
                k += 1

    plt.show()


def get_ax_name(ax_full):
    """
    Get name of axiom from a string 'ax_full' specifying both axiom and what it's applied to
    """
    for i, c in enumerate(ax_full):
        if c == " ":
            return ax_full[:i]
    return ax_full


def get_ax_param(ax_full):
    """
    Get parameters of axiom from a string 'ax_full' specifying both axiom and what it's applied to
    """
    for i, c in enumerate(ax_full):
        if c == " ":
            return ax_full[i+1:]
    return ""


def remove_brackets(str_):
    """
    Remove brackets in front of and after str_
    """
    for i, c in enumerate(str_):
        if c != '[':
            break
    for j in range(len(str_)-1,-1,-1):
        if str_[j] != ']':
            break
    return str_[i:j+1]


def make_tuple(abs_str):
    """
    Given abs_str (e.g. '[[comm-assoc]-[eval-mul1]]'), return tuple of the involved axioms ('comm', 'assoc', 'eval', 'mul1')
    """
    return tuple(map(remove_brackets, abs_str.split('-')))


def make_abs_str(abs_tuple):
    """
    Given abs_tuple (e.g. 'comm', 'assoc', 'eval', 'mul1'), return string of the involved axioms ('[comm-assoc-eval-mul1]')
    """
    return '-'.join(abs_tuple)


def make_param_str(param_tuple):
    """
    Given param_tuple, return string that joins parameters together with semicolon (;)
    """
    return '; '.join(param_tuple)


def is_prefix(pre, whole):
    """
    Return whether 'pre' (tuple) is prefix of 'whole' (tuple)
    """
    if len(pre) >= len(whole):
        return False
    for i, elt in enumerate(pre):
        if elt != whole[i]:
            return False
    return True


def prefix_get(pre, list_whole):
    """
    Return list of elements in 'list_whole' such that 'pre' is a prefix of them
    """
    return [elt for elt in list_whole if is_prefix(pre, elt)]


class Trie:
    def __init__(self, key=None):
        self.key = key
        self.is_term = False
        self.children = {}

    def find(self, keys):
        node = self
        for key in keys:
            node = node.children.get(key)
            if node is None:
                return None
        return node if node.is_term else None

    def add(self, keys):
        # find deepest
        node = self
        path_exists = True
        for i, key in enumerate(keys):
            if node.children.get(key) is None:
                path_exists = False
                break
            node = node.children[key]

        if path_exists:
            node.is_term = True
        else: # create remaining path
            old_child = Trie(keys[-1])
            old_child.is_term = True
            for j in range(len(keys)-2, i-1, -1):
                new_child = Trie(keys[j])
                new_child.children[old_child.key] = old_child
                old_child = new_child
            node.children[old_child.key] = old_child


def make_abs_trie(abstractions):
    """
    Convert abstractions into trie
    """
    trie = Trie()
    for ab in abstractions:
        trie.add(tuple(key for key in ab))
    return trie


def split_to_tree(string, div='~', delim="{}", transform=lambda x, info=None: x, info_mark=None):
    """
    Parses tree given in `string` with dividers `div` and delimiters `delim`
    Stores tree in nested structure given by `transform`
    `transform`: `transform(node, info) gives node data structure from `node` (e.g. tuple of nodes or just a single element) and additional info
    `info_mark`: character (e.g. ':') between tree and info associated with it

    >>> split_to_tree(r"abc-/def|52\-//g-h|8\-ij\|978", div='-', delim="/\\\\", transform=lambda x, info=None: x if isinstance(x, str) else '{' + '~'.join(x) + ('' if info is None else f":{info}") + '}', info_mark='|')
    '{abc~{def:52}~{{g~h:8}~ij}:978}'
    >>> split_to_tree("(+1-617)-253-1212", div='-', delim="()", transform=lambda x: x)
    [['+1', '617'], '253', '1212']
    """
    assert len(div) == 1 and len(delim) == 2 and (info_mark is None or len(info_mark) == 1)

    brkt_map = {}  # maps '{' index to '}' index
    depth_map = {}  # maps depth to '{' index
    d = 0
    for i, c in enumerate(string):
        if c == delim[0]:
            d += 1
            depth_map[d] = i
        elif c == delim[1]:
            brkt_map[depth_map[d]] = i
            d -= 1
            if d < 0:
                raise Exception("Mismatching brackets")
    if d > 0:
        raise Exception("Mismatching brackets")
    
    return split_to_tree_helper(string, brkt_map, div, delim, transform, info_mark)
    

def split_to_tree_helper(string, brkt_map, div, delim, transform, info_mark, i=-1, j=None):
    """
    Returns tuple of objects/tuples in string between indices i and j = brkt_map[i]
    string[i] should be '{'
    brkt_map maps '{' to '}'
    Default: parses entire string
    """
    j = len(string) if j is None else j
    arr = []
    l = i + 1
    while True:
        if string[l] == delim[0]:
            r = brkt_map[l]
            arr.append(split_to_tree_helper(string, brkt_map, div, delim, transform, info_mark, l, r))
            r += 1
        else:
            r = l
            while r < j and string[r] != div and string[r] != info_mark:
                r += 1
            arr.append(transform(string[l:r]))
        if r == j:
            return transform(arr)
        elif string[r] == info_mark:
            info = string[r+1:j]
            return transform(arr, info)
        assert string[r] == div
        l = r + 1
    

if __name__ == "__main__":
    # solutions = load_solutions("equations-8k.json")
    # print_solution(solutions[0])
    doctest.testmod()

    # trie = Trie()
    # trie.add(("my", "name", "is", "dumb"))
    # trie.add(("your", "name", "is"))
    # trie.add(("my", "age", "is", 13))
    # trie.add(("my", "name", "bruh"))
    # trie.add(("my", "name", "is"))
    # trie.add(("my", "name", "is", "very", "dumb"))

    # my = trie.children['my']
    # myname = my.children['name']
    # mynameis = myname.children['is']
    # myage = my.children['age']
    # your = trie.children['your']
    # yourname = your.children['name']

    # trie = Trie()
    # trie.add((1, 2))
    # trie.add((1, 3))
 
    # one = trie.children[1]

    import json

    with open("mathematical-abstractions/abstractions/IterAbsPair-8k.json") as f:
        abs = json.load(f)['axioms']
    trie = make_abs_trie(abs)
