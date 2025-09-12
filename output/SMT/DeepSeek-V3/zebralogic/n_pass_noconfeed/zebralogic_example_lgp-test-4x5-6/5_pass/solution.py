solver.add(Implies(education_vars[i] == bachelor_idx, flower_vars[i] == daffodils_idx))
solver.add(Implies(flower_vars[i] == daffodils_idx, education_vars[i] == bachelor_idx))