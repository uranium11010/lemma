# Learning Mathematical Abstractions from Formal Solutions

In this project, we want to learn mathematical abstractions from formal solutions generated algorithmically. These are some of the research questions we can explore:

1. Are there expressive patterns in these solutions? How should we represent and uncover them?
2. Can we recognize what operations these patterns carry out in terms of intuitive actions? For instance, "evaluating a large sub-expression" involves invoking evaluation operations often, whereas or "cancelling two equal terms" might involve repeatedly using commutativity and associativity until the terms are grouped together, then invoking a cancelation action.
3. If we rewrite long solutions in terms of the learned patterns, do they look natural?
4. Can these abstractions help us solve increasingly complex mathematical problems?

This is an initial dataset of [ConPoLe solutions to equations](https://drive.google.com/file/d/1-5SPDOIrxQ7jpC34sVOTbDfKVxRAJPxY/view?usp=sharing) ([larger version](https://drive.google.com/file/d/11M5ceRy7n3pnX2ORwWXE0uNdgLziSVMm/view?usp=sharing))
that we can use to explore questions 1-3. Question 4 will also require integrating the patterns in the learning algorithm.

A first attempt to find patterns could be something on these lines:

1. Represent each solution as a sequence of axioms (initially ignoring parameters)
2. Count the frequency of each contiguous subsequence of axioms in all solutions.
3. Rank these subsequences by a combination of (a) their frequency and (b) their length
4. Save the top pattern into a learned abstraction, creating a rewrite rule (sequence -> new abstract action).
5. Rewrite solutions using this new abstraction, then repeat K times.

