# Check if the constraints are satisfiable
if solver.check() == z3.sat:
    model = solver.model()
    bf = z3.is_true(model.eval(barbara_first))  # Correct way to get Python boolean

    b_start = model.eval(B_start).as_long()
    b_end = model.eval(B_end).as_long()
    k_start = model.eval(K_start).as_long()
    k_end = model.eval(K_end).as_long()