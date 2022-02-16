"""
Provides tools for dealing with ConPoLe solutions
"""

import json
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

