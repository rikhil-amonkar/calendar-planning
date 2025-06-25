from z3 import *

# Define the time spent at each location
time_fishermans_wharf = Int('time_fishermans_wharf')
time_nob_hill = Int('time_nob_hill')

# Define the constraints
s = Optimize()
s.add(0 <= time_fishermans_wharf)  # Time spent at Fisherman's Wharf is non-negative
s.add(time_fishermans_wharf <= 480)  # Time spent at Fisherman's Wharf is at most 480 minutes (8 hours)
s.add(0 <= time_nob_hill)  # Time spent at Nob Hill is non-negative
s.add(time_nob_hill <= 480)  # Time spent at Nob Hill is at most 480 minutes (8 hours)
s.add(time_fishermans_wharf + time_nob_hill >= 90)  # Meet Kenneth for at least 90 minutes
s.add(time_fishermans_wharf + time_nob_hill <= 540)  # Meet Kenneth before 9:00 PM
s.add(time_fishermans_wharf >= 90)  # Start meeting Kenneth at least 90 minutes after arriving at Fisherman's Wharf
s.add(time_nob_hill >= 135)  # Start meeting Kenneth at Nob Hill at least 135 minutes (2:15 PM) after arriving at Fisherman's Wharf
s.add(time_nob_hill <= 270)  # Finish meeting Kenneth at Nob Hill at most 270 minutes (5:30 PM) after arriving at Fisherman's Wharf

# Define the objective function
s.minimize((time_fishermans_wharf + time_nob_hill) / 2)  # Optimize the average time spent at both locations

# Solve the optimization problem
if s.check() == sat:
    model = s.model()
    print("Optimal schedule:")
    print(f"Time spent at Fisherman's Wharf: {model[time_fishermans_wharf]} minutes")
    print(f"Time spent at Nob Hill: {model[time_nob_hill]} minutes")
else:
    print("No solution found")