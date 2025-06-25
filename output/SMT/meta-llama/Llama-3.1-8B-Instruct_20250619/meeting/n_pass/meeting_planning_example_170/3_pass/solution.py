from z3 import *

# Define the variables
start_time = Int('start_time')
meet_emily = Int('meet_emily')
meet_margaret = Int('meet_margaret')

# Define the constraints
s = Optimize()
s.add(start_time >= 0)
s.add(meet_emily >= 0)
s.add(meet_emily <= 60)
s.add(meet_margaret >= 0)
s.add(meet_margaret <= 120)

# Define the time constraints for Emily and Margaret
emily_start = 4 * 60
emily_end = 5 * 60
margaret_start = 7 * 60
margaret_end = 9 * 60
s.add(emily_start <= start_time + meet_emily)
s.add(start_time + meet_emily <= emily_end)
s.add(margaret_start <= start_time + meet_margaret)
s.add(start_time + meet_margaret <= margaret_end)

# Define the objective function to minimize the total time
s.minimize(start_time + meet_emily + meet_margaret)

# Solve the optimization problem
solution = s.check()
if solution == sat:
    model = s.model()
    print(f"Best schedule: Meet Emily at {(model[meet_emily].as_long())} minutes after 9:00AM and meet Margaret at {(model[meet_margaret].as_long())} minutes after 9:00AM.")
    print(f"Total time: {(model[start_time].as_long() + model[meet_emily].as_long() + model[meet_margaret].as_long())} minutes")
else:
    print("No solution found")