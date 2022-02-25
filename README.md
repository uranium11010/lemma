# Learning Mathematical Abstractions from Formal Solutions

In this project, we want to learn mathematical abstractions from formal solutions generated algorithmically. These are some of the research questions we can explore:

1. Are there expressive patterns in these solutions? How should we represent and uncover them?
2. Can we recognize what operations these patterns carry out in terms of intuitive actions? For instance, "evaluating a large sub-expression" involves invoking evaluation operations often, whereas or "cancelling two equal terms" might involve repeatedly using commutativity and associativity until the terms are grouped together, then invoking a cancelation action.
3. If we rewrite long solutions in terms of the learned patterns, do they look natural?
4. Can these abstractions help us solve increasingly complex mathematical problems?

This is an initial dataset of [ConPoLe solutions to equations](https://drive.google.com/file/d/1-5SPDOIrxQ7jpC34sVOTbDfKVxRAJPxY/view?usp=sharing) ([larger version](https://drive.google.com/file/d/11M5ceRy7n3pnX2ORwWXE0uNdgLziSVMm/view?usp=sharing))
that we can use to explore questions 1-3. Question 4 will also require integrating the patterns in the learning algorithm.

Possible approaches:

Approach 1:
1. Represent each solution as a sequence of axioms (initially ignoring parameters)
2. Count the frequency of each contiguous subsequence of axioms in all solutions.
3. Rank these subsequences by a combination of (a) their frequency and (b) their length
4. Save the top pattern into a learned abstraction, creating a rewrite rule (sequence -> new abstract action).
5. Rewrite solutions using this new abstraction, then repeat K times.

Approach 1 variant: (currently implemented in `IterAbsPairs` class in `compress.py`)
1. Represent each solution as a sequence of axioms (initially ignoring parameters)
2. Count the frequency of each contiguous length-2 subsequence of axioms in all solutions.
3. Rank these subsequences by a combination of their frequency
4. Save the top pattern (or top few, based on threshold) into a learned abstraction, creating a rewrite rule (sequence -> new abstract action).
5. Rewrite solutions using this new abstraction, then repeat K times.

Approach 2: (currently implemented in `CommonPairs` class in `compress.py`)
1. Represent each solution as a sequence of axioms (initially ignoring parameters).
2. Count the frequency of contiguous pairs of actions among the dataset of solutions.
3. Construct directed graph where edges point from a current action to a next action where the frequency is at least some threshold frequency.
4. Find maximal paths within the graph, although the term "maximal" is not well-defined when the graph has cycles. (So we need some better definition here.)
Issues: A->B common and B->C common doesn't imply that A->B->C is common; currently, many redundancies in the paths generated (e.g. if A->B->C is an outputed abstraction, B->C would also be an outputed abstraction).

### Next steps

1. Improve Approach 2: remove redundancies
2. Implement Approach 1. Two specific approaches:
    1. Store all occurring subsequences in solutions in dictionary as keys, which is possible since a subsequence can be represented as a tuple of immutable objects; let values of dictionary = frequencies); takes up a lot of memory--have cut-off length?
    2. Iteratively find common subsequences of length 2, 3, 4, etc. using cut-off frequency threshold; after length k, only look for length-(k+1) subsequences that have the first k elements being a common subsequence and last k elements being a common subsequence
3. Implement abstraction on the solutions to see if the abstracted solutions look good
4. Tool function that draws weighted graph of frequencies of action pairs
