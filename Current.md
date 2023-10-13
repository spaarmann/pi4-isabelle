# To talk about

- Should I change header_table to be "instanc => header_type"?
  Having optional results for this mapping complicates various things in annoying ways, and I think
  for questionable benefit. Effectively we would just assume that all instances referenced are
  actually defined, which is a trivial syntactic check that could be done ahead of time. This could
  be encapsulated by the well-formedness predicate if we had it, though the thesis doesn't even
  bother including it.

# Questions/help