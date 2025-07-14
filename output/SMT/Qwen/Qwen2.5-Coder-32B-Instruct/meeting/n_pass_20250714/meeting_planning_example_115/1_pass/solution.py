from z3 import *

# Define the time variables for each location visit
t_richmond = Int('t_richmond')
t_pacific_heights = Int('t_pacific_heights')
t_marina_district = Int('t_marina_district')

# Create a solver instance
solver = Solver()

# Add constraints based on the problem statement
# Initial constraint: Start at Richmond District at 9:00 AM (540 minutes after midnight)
solver.add(t_richmond == 540)

# Constraints for meeting Carol for at least 60 minutes between 11:30 AM and 3:00 PM (690 to 1800 minutes)
solver.add(Or(And(t_marina_district >= 690, t_marina_district + 60 <= 1800),
              And(t_pacific_heights >= 690, t_pacific_heights + 60 <= 1800)))

# Constraints for meeting Jessica for at least 45 minutes between 3:30 PM and 4:45 PM (2130 to 2670 minutes)
solver.add(Or(And(t_marina_district >= 2130, t_marina_district + 45 <= 2670),
              And(t_pacific_heights >= 2130, t_pacific_heights + 45 <= 2670)))

# Travel time constraints
# Richmond to Pacific Heights: 10 minutes
solver.add(t_pacific_heights >= t_richmond + 10)
# Richmond to Marina District: 9 minutes
solver.add(t_marina_district >= t_richmond + 9)
# Pacific Heights to Richmond District: 12 minutes
solver.add(t_richmond >= t_pacific_heights + 12)
# Pacific Heights to Marina District: 6 minutes
solver.add(t_marina_district >= t_pacific_heights + 6)
# Marina District to Richmond District: 11 minutes
solver.add(t_richmond >= t_marina_district + 11)
# Marina District to Pacific Heights: 7 minutes
solver.add(t_pacific_heights >= t_marina_district + 7)

# Objective: Maximize the number of friends met
# We'll add soft constraints to prioritize meeting both friends
meet_carol = Or(And(t_marina_district >= 690, t_marina_district + 60 <= 1800),
                And(t_pacific_heights >= 690, t_pacific_heights + 60 <= 1800))
meet_jessica = Or(And(t_marina_district >= 2130, t_marina_district + 45 <= 2670),
                  And(t_pacific_heights >= 2130, t_pacific_heights + 45 <= 2670))

# Use Optimize instead of Solver to handle soft constraints
opt = Optimize()
opt.add(solver.assertions())
opt.maximize(If(meet_carol, 1, 0) + If(meet_jessica, 1, 0))

# Check if the solution is satisfiable
if opt.check() == sat:
    model = opt.model()
    print("SOLUTION:")
    print(f"Visit Richmond District at: {model[t_richmond]} minutes after midnight")
    print(f"Visit Pacific Heights at: {model[t_pacific_heights]} minutes after midnight")
    print(f"Visit Marina District at: {model[t_marina_district]} minutes after midnight")
else:
    print("No solution found")