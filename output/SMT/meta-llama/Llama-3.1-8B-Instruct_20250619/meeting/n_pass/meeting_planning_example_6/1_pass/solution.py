from z3 import *

# Define the variables
meet_kenneth = Bool('meet_kenneth')
time_at_nob_hill = Int('time_at_nob_hill')
time_at_fishermans_wharf = Int('time_at_fishermans_wharf')

# Define the constraints
s = Solver()
s.add(meet_kenneth == (time_at_nob_hill >= 215) & (time_at_nob_hill <= 745) & (time_at_fishermans_wharf - time_at_nob_hill >= 90))
s.add(time_at_nob_hill >= 215)  # Kenneth is available from 2:15PM
s.add(time_at_nob_hill <= 745)  # Kenneth is available until 7:45PM
s.add(time_at_fishermans_wharf >= 900)  # We arrive at Fisherman's Wharf at 9:00AM
s.add(time_at_nob_hill >= 900)  # We arrive at Nob Hill after 9:00AM
s.add(time_at_fishermans_wharf - time_at_nob_hill <= 720)  # We arrive back at Fisherman's Wharf within 12 hours

# Define the objective function
s.add(meet_kenneth == True)  # We want to meet Kenneth for a minimum of 90 minutes

# Solve the problem
if s.check() == sat:
    model = s.model()
    print("We meet Kenneth at Nob Hill at", model[time_at_nob_hill].as_long(), "and arrive back at Fisherman's Wharf at", model[time_at_fishermans_wharf].as_long())
else:
    print("No solution found")