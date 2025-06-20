from z3 import *

# Define the variables
meet_emily = Int('meet_emily')
meet_margaret = Int('meet_margaret')

# Define the constraints
s = Optimize()
s.add(meet_emily >= 45)
s.add(meet_emily <= 75) # 4:00PM to 5:15PM
s.add(meet_margaret >= 120)
s.add(meet_margaret <= 240) # 7:00PM to 9:00PM

# Define the objective function to minimize the total time
s.minimize(meet_emily + meet_margaret)

# Solve the optimization problem
solution = s.check()
if solution == sat:
    model = s.model()
    print(f"Best schedule: Meet Emily at {(model[meet_emily].as_long())} minutes after 9:00AM and meet Margaret at {(model[meet_margaret].as_long())} minutes after 9:00AM.")
    print(f"Total time: {(model[meet_emily].as_long() + model[meet_margaret].as_long())} minutes")
else:
    print("No solution found")