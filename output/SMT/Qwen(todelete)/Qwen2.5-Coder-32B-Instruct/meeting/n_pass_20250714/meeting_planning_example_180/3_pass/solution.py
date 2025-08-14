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
james_start = 765
james_end = 1200
james_meeting_time = 75

# Constraints for meeting Robert in The Castro from 12:45 PM to 3:15 PM (765 to 1890 minutes after midnight)
# Minimum 30 minutes meeting time
robert_start = 765
robert_end = 1890
robert_meeting_time = 30

# James meeting constraints
solver.add(And(t_md >= james_start, t_md + james_meeting_time <= james_end))

# Robert meeting constraints
solver.add(And(t_c >= robert_start, t_c + robert_meeting_time <= robert_end))

# Travel time constraints
# North Beach to Mission District: 18 minutes
solver.add(t_md >= t_nb + 18)
# North Beach to The Castro: 22 minutes
solver.add(t_c >= t_nb + 22)
# Mission District to North Beach: 17 minutes
solver.add(t_nb >= t_md + 17)
# Mission District to The Castro: 7 minutes
solver.add(t_c >= t_md + 7)
# The Castro to North Beach: 20 minutes
solver.add(t_nb >= t_c + 20)
# The Castro to Mission District: 7 minutes
solver.add(t_md >= t_c + 7)

# Ensure we meet both James and Robert
# We need to check if there is a feasible schedule where we can meet both
# Let's try to find a valid schedule by adjusting the arrival times

# Add constraints to ensure we can meet both James and Robert
# We need to find a time to meet James first and then Robert or vice versa

# Try meeting James first, then Robert
solver.push()
solver.add(t_md >= t_nb + 18)  # Arrive at Mission District after North Beach
solver.add(t_c >= t_md + 7)   # Arrive at The Castro after Mission District
solver.add(t_c + robert_meeting_time <= robert_end)  # Ensure we can meet Robert

if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    print(f"Arrive at North Beach at: {model[t_nb]} minutes (9:00 AM)")
    print(f"Arrive at Mission District at: {model[t_md]} minutes ({model[t_md] // 60}:{model[t_md] % 60:02d} AM/PM)")
    print(f"Arrive at The Castro at: {model[t_c]} minutes ({model[t_c] // 60}:{model[t_c] % 60:02d} AM/PM)")
else:
    solver.pop()
    # Try meeting Robert first, then James
    solver.add(t_c >= t_nb + 22)  # Arrive at The Castro after North Beach
    solver.add(t_md >= t_c + 7)   # Arrive at Mission District after The Castro
    solver.add(t_md + james_meeting_time <= james_end)  # Ensure we can meet James

    if solver.check() == sat:
        model = solver.model()
        print("SOLUTION:")
        print(f"Arrive at North Beach at: {model[t_nb]} minutes (9:00 AM)")
        print(f"Arrive at The Castro at: {model[t_c]} minutes ({model[t_c] // 60}:{model[t_c] % 60:02d} AM/PM)")
        print(f"Arrive at Mission District at: {model[t_md]} minutes ({model[t_md] // 60}:{model[t_md] % 60:02d} AM/PM)")
    else:
        print("No solution found")