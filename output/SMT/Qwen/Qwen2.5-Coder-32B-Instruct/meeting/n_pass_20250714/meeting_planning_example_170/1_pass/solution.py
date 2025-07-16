from z3 import *

# Define the solver
solver = Solver()

# Define variables for the times you arrive at each location
t_nb = Int('t_nb')  # Time arriving at North Beach
t_us = Int('t_us')  # Time arriving at Union Square
t_rh = Int('t_rh')  # Time arriving at Russian Hill

# Initial constraint: You arrive at North Beach at 9:00 AM (540 minutes after midnight)
solver.add(t_nb == 540)

# Constraints for meeting Emily at Union Square from 4:00 PM to 5:15 PM (1080 to 1155 minutes after midnight)
# You need to meet her for at least 45 minutes
solver.add(t_us + 45 <= 1155)  # Must finish meeting Emily by 5:15 PM
solver.add(t_us >= 1080)       # Must start meeting Emily by 4:00 PM

# Constraints for meeting Margaret at Russian Hill from 7:00 PM to 9:00 PM (1320 to 1440 minutes after midnight)
# You need to meet her for at least 120 minutes
solver.add(t_rh + 120 <= 1440)  # Must finish meeting Margaret by 9:00 PM
solver.add(t_rh >= 1320)        # Must start meeting Margaret by 7:00 PM

# Travel time constraints
# North Beach to Union Square: 7 minutes
solver.add(t_us >= t_nb + 7)
# North Beach to Russian Hill: 4 minutes
solver.add(t_rh >= t_nb + 4)
# Union Square to North Beach: 10 minutes
solver.add(t_nb >= t_us + 10)
# Union Square to Russian Hill: 13 minutes
solver.add(t_rh >= t_us + 13)
# Russian Hill to North Beach: 5 minutes
solver.add(t_nb >= t_rh + 5)
# Russian Hill to Union Square: 11 minutes
solver.add(t_us >= t_rh + 11)

# Objective: Maximize the number of friends met
# Since we have fixed meeting times for Emily and Margaret, we just need to check if we can meet them
# We will add soft constraints to prioritize meeting both friends
solver.add(Soft(t_us >= 1080))
solver.add(Soft(t_rh >= 1320))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    print(f"Arrive at North Beach: {model[t_nb]} minutes after midnight")
    print(f"Arrive at Union Square: {model[t_us]} minutes after midnight")
    print(f"Arrive at Russian Hill: {model[t_rh]} minutes after midnight")
else:
    print("No solution found")