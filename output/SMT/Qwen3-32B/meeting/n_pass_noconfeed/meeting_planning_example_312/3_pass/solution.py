solver = z3.Solver()
  solver.add(travel_time == 10)
  if solver.check() == z3.sat:
      print(solver.model())