"""
Provides tools for dealing with ConPoLe solutions
"""

import json
import warnings
import doctest
import numpy as np
import matplotlib.pyplot as plt


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


class Trie:
    def __init__(self, key=None, value=None, comment=None):
        self.key = key
        self.value = value
        self.comment = comment
        self.is_term = False
        self.children = {}

    def find(self, keys):
        node = self
        for key in keys:
            node = node.children.get(key)
            if node is None:
                return None
        return node if node.is_term else None

    def add(self, keys, value=None, comment=None):
        # find deepest
        node = self
        path_exists = True
        for i, key in enumerate(keys):
            if node.children.get(key) is None:
                path_exists = False
                break
            node = node.children[key]

        if path_exists:
            if node.is_term == True and node.value != value:
                warnings.warn("Changing value of existing key")
            node.is_term = True
            node.value = value
            node.comment = comment
            return node
        # create remaining path
        final_child = old_child = Trie(keys[-1], value, comment)
        old_child.is_term = True
        for j in range(len(keys)-2, i-1, -1):
            new_child = Trie(keys[j])
            new_child.children[old_child.key] = old_child
            old_child = new_child
        node.children[old_child.key] = old_child
        return final_child

    def __str__(self):
        # self_str = str(self.key)[:8] if self.value is None else str(self.key)[-4:] + ': ' + str(self.value)[:4]
        self_str = str(self.key) if self.value is None else str(self.key) + ': ' + str(self.value)
        if not self.children:
            return f"    {self_str}    "
        children = [list(reversed(str(child).split('\n'))) for child in self.children.values()]
        widths = [len(child[0]) for child in children]
        width = sum(widths)
        left_spaces = (width - len(self_str)) // 2 - 2
        right_spaces = (width - len(self_str) + 1) // 2 - 2
        out_str = '  ' + '_' * left_spaces + self_str + '_' * right_spaces + '  '
        while True:
            row = ''.join(child.pop() if child else ' ' * w for child, w in zip(children, widths))
            out_str += f"\n{row}"
            if all(not child for child in children):
                break
        return out_str


def make_rule_trie(rules):
    """
    Convert rules into trie
    """
    trie = Trie()
    for rule in rules:
        trie.add(list(rule), rule)
    return trie


class DoubleTrie:
    def __init__(self, append_key=None, prepend_key=None, value=None, comment=None, accum=False, depth=0):
        self.append_key = append_key
        self.prepend_key = prepend_key
        self.value = value
        self.comment = comment
        self.accum = accum  # if True, value of node is sum of children
        self.depth = depth
        self.is_term = False
        self.append_parent = None
        self.append_children = {}
        self.prepend_parent = None
        self.prepend_children = {}

    def find(self, keys, include_partial=False, debug=False):
        node = self
        for key in keys:
            node = node.append_children.get(key)
            if node is None:
                raise KeyError("Trie does not contain given key")
        if node.is_term or include_partial:
            if debug:
                rev_node = self
                for key in reversed(keys):
                    rev_node = rev_node.prepend_children.get(key)
                assert node is rev_node
            return node
        raise KeyError("Trie does not contain given key")

    def add(self, keys, value=None, rel_pos=None, comment=None, max_length=None):
        assert rel_pos is None or len(rel_pos) + 1 == len(keys)
        def make_children(cur_nodes, depth):
            final = depth == len(keys) - 1
            for i_a, i_p in zip(range(depth, len(keys)), range(len(keys)-depth)):
                key_a, key_p = keys[i_a], keys[i_p]
                if rel_pos is not None:
                    rel_pos_a = rel_pos[i_a-1] if depth > 0 else None
                    key_a = (rel_pos_a, key_a)
                    rel_pos_p = rel_pos[i_p] if depth > 0 else None
                    key_p = (key_p, rel_pos_p)
                node_a = cur_nodes[i_p]
                if (child := node_a.append_children.get(key_a)) is not None:
                    if final:
                        if not self.accum and child.is_term and child.value != value:
                            warnings.warn("Changing value of existing key")
                        child.is_term = True
                        if self.accum:
                            child.value += value
                        else:
                            child.value = value
                        child.comment = comment
                    elif self.accum:
                        child.value += value
                else:
                    node_p = cur_nodes[i_p+1]
                    child = DoubleTrie(key_a, key_p, value if self.accum or final else None,
                                       comment if final else None, self.accum, depth+1)
                    if final:
                        child.is_term = True
                    node_a.append_children[key_a] = child
                    node_p.prepend_children[key_p] = child
                    child.append_parent = node_a
                    child.prepend_parent = node_p
                yield child

        cur_nodes = [self for _ in range(len(keys) + 1)]
        if max_length is None:
            for depth in range(len(keys)):
                cur_nodes = list(make_children(cur_nodes, depth))
            return cur_nodes[0]
        for depth in range(min(len(keys), max_length)):
            cur_nodes = list(make_children(cur_nodes, depth))
        return cur_nodes

    def __hash__(self):
        return hash(self.append_parent) ^ hash(self.append_key)

    def get_str(self, prepend, compact=False):
        key = self.prepend_key if prepend else self.append_key
        
        def format_abs_elt(key):
            if key is None:
                return "None"
            if not compact:
                return str(key)
            def abbrev(ax):
                exceptions = {"sub_self": "sb", "sub_comm": "sc", "add0": "a0", "sub0": "s0", "mul1": "m1", "div1": "d1",
                              "div_self": "ds", "sub_self": "ss", "subsub": "ssb", "mul0": "m0", "zero_div": "zd"}
                if ax in exceptions:
                    return exceptions[ax]
                return ax[0]
            def format_rel_pos(rel_pos):
                if rel_pos is None:
                    return ''
                left = '$' if rel_pos[0] is None else rel_pos[0]
                right = '$' if rel_pos[1] is None else rel_pos[1]
                return left + '_' + right
            if prepend:
                return abbrev(str(key[0])) + format_rel_pos(key[1])
            return format_rel_pos(key[0]) + abbrev(str(key[1]))
        if self.value is None:
            self_str = format_abs_elt(key)
        else:
            value_str = str(self.value) if not compact else "{:.1f}".format(self.value)
            self_str = format_abs_elt(key) + ': ' + value_str
        self_str = f'|{self_str}|' if self.is_term else self_str
        children_nodes = self.prepend_children if prepend else self.append_children
        if not children_nodes:
            return f"    {self_str}    "
        children = [list(reversed(child.get_str(prepend, compact).split('\n'))) for child in children_nodes.values()]
        widths = [len(child[0]) for child in children]
        width = sum(widths)
        left_spaces = (width - len(self_str)) // 2 - 2
        right_spaces = (width - len(self_str) + 1) // 2 - 2
        out_str = '  ' + '_' * left_spaces + self_str + '_' * right_spaces + '  '
        while True:
            row = ''.join(child.pop() if child else ' ' * w for child, w in zip(children, widths))
            out_str += f"\n{row}"
            if all(not child for child in children):
                break
        return out_str

    def __str__(self, compact=None):
        compact = len(self.append_children) >= 5
        return self.get_str(False, compact) + '\n\n' + self.get_str(True, compact)


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
    # doctest.testmod()

    # trie = DoubleTrie(accum=True)
    # trie.add(('a', 'b', 'c', 'd'), 1, max_length=4)
    # trie.add(('e', 'b', 'c'), 10, max_length=4)
    # trie.add(('a', 'f', 'c', 'g'), 100, max_length=4)
    # trie.add(('a', 'b', 'a'), 1000, max_length=4)
    # trie.add(('a', 'b', 'c'), 10000, max_length=4)
    # trie.add(('a', 'b', 'c', 'c', 'd'), 100000, max_length=4)
    # trie.add(('b', 'c', 'd', 'b', 'e', 'c', 'd'), 1000000, max_length=4)
    # print(trie)
    from abstractions import Axiom, AxiomSeq, AxSeqTreeRelPos
    rules = [Axiom('a', AxiomSeq), Axiom('b', AxiomSeq), Axiom('c', AxiomSeq), AxiomSeq.from_string('a~b'), AxiomSeq.from_string('c~b')]
    print(make_rule_trie(rules))
    rules = [Axiom('a', AxSeqTreeRelPos), Axiom('b', AxSeqTreeRelPos), Axiom('c', AxSeqTreeRelPos), AxSeqTreeRelPos.from_string('a~b:_1'), AxSeqTreeRelPos.from_string('c~b:1_')]
    print(make_rule_trie(rules))
