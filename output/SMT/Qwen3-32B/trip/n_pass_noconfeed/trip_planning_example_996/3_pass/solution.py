from z3 import Solver, Int, If, AllDifferent

# Initialize the solver
solver = Solver()

# Define the order as a list of symbolic integer variables
order = [Int(f'order_{i}') for i in range(7)]

# Optionally add constraint that each city is visited exactly once
solver.add(AllDifferent(order))

# Define start_days as symbolic integer variables
start_days = [Int(f'start_{i}') for i in range(7)]

# Duration lookup using If expressions
for i in range(1, 7):
    prev_city = order[i - 1]
    duration_prev = If(prev_city == 0, 3,
                       If(prev_city == 1, 2,
                          If(prev_city == 2, 5,
                             If(prev_city == 3, 3,
                                If(prev_city == 4, 5,
                                   If(prev_city == 5, 5,
                                      If(prev_city == 6, 5, 0)))))))
    solver.add(start_days[i] == start_days[i - 1] + duration_prev - 1)

# Duration for the last city
last_city = order[6]
duration_last = If(last_city == 0, 3,
                   If(last_city == 1, 2,
                      If(last_city == 2, 5,
                         If(last_city == 3, 3,
                            If(last_city == 4, 5,
                               If(last_city == 5, 5,
                                  If(last_city == 6, 5, 0)))))))
end_day_last = start_days[6] + duration_last - 1
solver.add(end_day_last == 22)

# Now you can check for a solution
if solver.check() == sat:
    model = solver.model()
    print("Solution found:")
    for i in range(7):
        print(f"City {model[order[i]]} starts on day {model[start_days[i]]}")
else:
    print("No solution found.")