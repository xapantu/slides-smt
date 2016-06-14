Counting constraints in SMT, a step towards model checking of fault tolerant
systems.

Parametrized model checking helps to study the properties of a system with an
arbitrary number of processes. Assuming that a fraction of those processes are
faulty is needed to guarantee safety of a real-life system.
Sally is a model checker for infinite state systems developed at SRI. It can use
various SMT solvers to check the properties of a given system. We aim to
provide a way to check those fault tolerant parametrized systems with Sally.
Counting constraints can be used at the SMT solver level to specify how many
processes can be faulty.
Through the example of the Byzantine generals, I will give a short introduction
of Sally, explain why counting constraints can help to solve this problem and how
we started implementing them in an SMT solver.

