# Learning Mathematical Abstractions from Formal Solutions

In this project, we want to learn mathematical abstractions from formal solutions generated algorithmically. These are some of the research questions we can explore:

1. Are there expressive patterns in these solutions? How should we represent and uncover them?
2. Can we recognize what operations these patterns carry out in terms of intuitive actions? For instance, "evaluating a large sub-expression" involves invoking evaluation operations often, whereas or "cancelling two equal terms" might involve repeatedly using commutativity and associativity until the terms are grouped together, then invoking a cancelation action.
3. If we rewrite long solutions in terms of the learned patterns, do they look natural?
4. Can these abstractions help us solve increasingly complex mathematical problems?

This is an initial dataset of [ConPoLe solutions to equations](https://drive.google.com/file/d/1-5SPDOIrxQ7jpC34sVOTbDfKVxRAJPxY/view?usp=sharing) ([larger version](https://drive.google.com/file/d/11M5ceRy7n3pnX2ORwWXE0uNdgLziSVMm/view?usp=sharing))
that we can use to explore questions 1-3. Question 4 will also require integrating the patterns in the learning algorithm.

## Types of abstractions

`abstractions.py` contains interfaces for three kinds of abstraction that incorporate slightly different information in the abstraction:
* `tree_rel_pos` (class `AxSeqTreePos`): Specifies a sequence of axioms and the relative positions of application in the expression tree.
* `dfs_idx_rel_pos` (class `AxSeqRelPos`): Specifies a sequence of axioms and the relative positions of application according to the old DFS indexing by ConPoLe
* `ax_seq` (class `AxiomSeq`): Specifies a sequence of axioms

## Abstraction algorithms

`compress.py` contains implementations of three algorithms for discovering abstractions from a data set of ConPoLe solutions.
* `CommonPairs`: (WARNING: COMPELTELY DEPRECATED)
  1. Represent each solution as a sequence of axioms (initially ignoring parameters).
  2. Count the frequency of contiguous pairs of actions among the dataset of solutions.
  3. Construct directed graph where edges point from a current action to a next action where the frequency is at least some threshold frequency.
  4. Find maximal paths within the graph, although the term "maximal" is not well-defined when the graph has cycles. (So we need some better definition here.)

Issues: A->B common and B->C common doesn't imply that A->B->C is common; currently, many redundancies in the paths generated (e.g. if A->B->C is an outputed abstraction, B->C would also be an outputed abstraction).

* `IterAbsPairs`:
  1. Represent each solution as a sequence of axioms (initially ignoring parameters)
  2. Count the frequency of each possible length-2 abstraction in all solutions. Recall that a length-2 abstraction is any combination of a contiguous length-2 subsequence of axioms + possibly information regarding the relative positions of application of the two axioms, depending on the type of abstraction.
  3. Rank these abstractions by their frequencies
  4. Save the top t abstractions (or set a threshold frequency for inclusion) into learned abstractions, creating a rewrite rule (sequence of axioms -> new abstract action).
  5. Rewrite solutions using these new abstractions, then repeat K times, each time adding t more abstractions.

* `IAPHolistic`: Same as `IterAbsPairs`, but with two modifications.
  * Abstractions are not ranked by their frequencies, but by a "holistic score" defined by frequency * (abstraction depth + abstraction length)
    - *Note:* Since we create abstractions of abstractions while iterating the abstraction process, every abstraction is viewed as a tree. "Abstraction depth" refers to the height of this tree.
  * While iterating the abstraction process, in addition to considering abstractions of the form A1 + A2 where A1 and A2 are axioms or abstractions that we've previously discovered, we consider "flattened" versions of these abstractions, i.e., (axioms/abstractions that make up A1) + (axioms/abstractions that make up A2). This is to relax the constraint that all abstraction trees are binary trees.
  * We always only keep the top t abstractions, so as we add more abstractions during the iteration process, abstractions with low scores would be removed. As such, specifying the number of iterations allows us to tune the degree of abstraction performed.

## Running the code

All implementations use Python 3. There are no requirements additional to the Python standard library.

Running the following command discovers abstractions from a data set of ConPoLe solutions:
```
python compress.py [-h] [--file FILE] [--sol-file SOL_FILE] [--use NUM_USE] [--store NUM_STORE] [--num-ex-sol NUM_EX_SOL] [-s] [--iter ITER] [--thres THRES] [--top K] [--hol] [--tree] [--pos] [--peek] [-v]
```
* `--file`: Path to store the abstractions (should end in `.json` or `.pkl`)
* `--sol-file`: Path to store the abstracted solutions (should end in `.pkl`)
* `--use`: How many solutions to learn abstractions from (default: all in the file of solutions provided, i.e., 80k, or 8k if `-s` is specified)
* `--store`: How many abstracted solutions to store (default: all solutions abstracted from those in the file of solutions provided)
* `--num-ex-sol`: Number of example abstracted solutions to print to the terminal (default: `0`)
* `-s`: Specfying this option will use the small data set of 8k solutions for discovering abstractions, as opposed to the regular data set of 80k solutions
* `--iter`: Number of iterations of abstraction to perform in `IterAbsPair` or `IAPHolistic` (default: `1`)
* `--thres`: Threshold frequency (average number of occurrences per solution) for `IterAbsPair` or theshold score for `IAPHolistic`
* `--top K`: Take the top K abstractions. (*Note:* One should specify only one of `--top` and `--thres`.)
* `--hol`: Specifying this option will use `IAPHolistic`. The default is `IterAbsPairs`.
* `--tree`: Use `tree_rel_pos` abstractions.
* `--pos`: Use `dfs_idx_rel_pos` abstractions. (*Note:* Specifying neither of `--tree` or `--pos` would use `ax_seq` abstractions.)
* `--peek`: If using `ax_seq` abstractions with `IterAbsPairs`, specifying this option allows you to take a peek at the frequencies of different relative position for an abstraction.
* `-v` (verbose): Specifying this option will print the discovered abstractions along with their frequencies/scores and an example occurrence for each abstraction. Not specifying the option will only print the abstractions with their frequencies/scores.

Here's an example that discovers and saves the top 8 length-2 `tree_rel_pos` abstractions using the `IterAbsPairs` algorithm:
```
python compress.py --file abstractions/IAP-80k-8len2-tree.json --top 8 --tree
```
Note that not specifying `--iter` defaults it to 1 so that the generated abstractions are of length 2.
