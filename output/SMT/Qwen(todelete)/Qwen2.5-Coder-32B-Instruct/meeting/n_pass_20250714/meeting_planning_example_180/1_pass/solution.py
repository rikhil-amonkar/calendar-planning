from z3 import *

# Define the solver
solver = Solver()

# Define the time variables for arriving at each location
t_nb = Int('t_nb')  # Time arriving at North Beach
t_md = Int('t_md')  # Time arriving at Mission District
t_c = Int('t_c')    # Time arriving at The Castro

# Initial constraint: You arrive at North Beach at 9:00 AM (540 minutes after midnight)
solver.add(t_nb == 540)

# Constraints for meeting James in the Mission District from 12:45 PM to 2:00 PM (765 to 1200 minutes after midnight)
# Minimum 75 minutes meeting time
solver.add(And(t_md >= 765, t_md + 75 <= 1200))

# Constraints for meeting Robert in The Castro from 12:45 PM to 3:15 PM (765 to 1890 minutes after midnight)
# Minimum 30 minutes meeting time
solver.add(And(t_c >= 765, t_c + 30 <= 1890))

# Travel time constraints
# North Beach to Mission District: 18 minutes
solver.add(t_md - t_nb >= 18)
# North Beach to The Castro: 22 minutes
solver.add(t_c - t_nb >= 22)
# Mission District to North Beach: 17 minutes
solver.add(t_nb - t_md >= 17)
# Mission District to The Castro: 7 minutes
solver.add(t_c - t_md >= 7)
# The Castro to North Beach: 20 minutes
solver.add(t_nb - t_c >= 20)
# The Castro to Mission District: 7 minutes
solver.add(t_md - t_c >= 7)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    print(f"Arrive at North Beach at: {model[t_nb]} minutes (9:00 AM)")
    print(f"Arrive at Mission District at: {model[t_md]} minutes ({model[t_md] // 60}:{model[t_md] % 60:02d} AM/PM)")
    print(f"Arrive at The Castro at: {model[t_c]} minutes ({model[t_c] // 60}:{model[t_c] % 60:02d} AM/PM)")
else:
    print("No solution found")