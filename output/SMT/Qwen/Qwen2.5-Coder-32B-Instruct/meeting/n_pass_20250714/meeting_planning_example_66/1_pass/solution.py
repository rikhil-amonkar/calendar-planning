from z3 import *

# Create a solver instance
solver = Solver()

# Define time variables in minutes since 9:00 AM
leave_nob_hill = Int('leave_nob_hill')
arrive_presidio = Int('arrive_presidio')
leave_presidio = Int('leave_presidio')
arrive_nob_hill = Int('arrive_nob_hill')

# Constraints
# You arrive at Nob Hill at 9:00 AM (0 minutes)
solver.add(leave_nob_hill >= 0)

# Travel time from Nob Hill to Presidio is 17 minutes
solver.add(arrive_presidio == leave_nob_hill + 17)

# Robert is available from 11:15 AM to 5:45 PM
# 11:15 AM is 135 minutes after 9:00 AM
# 5:45 PM is 465 minutes after 9:00 AM
solver.add(arrive_presidio >= 135)
solver.add(leave_presidio <= 465)

# You need to meet Robert for at least 120 minutes
solver.add(leave_presidio - arrive_presidio >= 120)

# Travel time from Presidio to Nob Hill is 18 minutes
solver.add(arrive_nob_hill == leave_presidio + 18)

# Objective: Minimize the total time spent traveling and meeting Robert
# Since we don't have a specific end time, we can just find a feasible schedule
if solver.check() == sat:
    model = solver.model()
    leave_nob_hill_time = model[leave_nob_hill].as_long()
    arrive_presidio_time = model[arrive_presidio].as_long()
    leave_presidio_time = model[leave_presidio].as_long()
    arrive_nob_hill_time = model[arrive_nob_hill].as_long()

    print(f"Leave Nob Hill at: {leave_nob_hill_time} minutes past 9:00 AM")
    print(f"Arrive Presidio at: {arrive_presidio_time} minutes past 9:00 AM")
    print(f"Leave Presidio at: {leave_presidio_time} minutes past 9:00 AM")
    print(f"Arrive Nob Hill at: {arrive_nob_hill_time} minutes past 9:00 AM")
else:
    print("No solution found")