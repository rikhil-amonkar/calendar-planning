from z3 import *

# Define the time variables
arrival_time = 9 * 60  # 9:00 AM in minutes
timothy_start = 20 * 60 + 45  # 8:45 PM in minutes
timothy_end = 20 * 60 + 90  # 9:30 PM in minutes
min_meeting_duration = 45  # Minimum meeting duration in minutes

# Create a solver instance
solver = Solver()

# Define the visit times for each location
visit_alamo_square = Int('visit_alamo_square')
visit_richmond_district = Int('visit_richmond_district')

# Constraints
# You start at Alamo Square at 9:00 AM
solver.add(visit_alamo_square == arrival_time)

# Travel time constraints
# If you visit Richmond District, you must account for travel time from Alamo Square
# and back to Alamo Square
solver.add(visit_richmond_district >= visit_alamo_square + 12)
solver.add(visit_alamo_square >= visit_richmond_district + 13)

# Meeting Timothy constraint
# You need to meet Timothy for at least 45 minutes between 8:45 PM and 9:30 PM
# This means you must be in Richmond District during this time for at least 45 minutes
solver.add(visit_richmond_district <= timothy_start - min_meeting_duration)
solver.add(visit_richmond_district + min_meeting_duration >= timothy_end)

# Objective: Maximize the number of friends met
# Since the problem is simplified and we only have two locations, we aim to maximize
# the time spent in Richmond District within the given constraints
# We add a soft constraint to maximize the time spent in Richmond District
maximize_richmond_time = Int('maximize_richmond_time')
solver.add(maximize_richmond_time == visit_richmond_district + min_meeting_duration - timothy_start)

# Optimize the solver
h = Optimize()
h.add(solver.assertions())
h.minimize(maximize_richmond_time)  # Minimizing the negative of the time spent in Richmond District

# Check if the problem is solvable
if h.check() == sat:
    m = h.model()
    print("SOLUTION:")
    print(f"Visit Alamo Square at: {m[visit_alamo_square].as_long()} minutes past midnight")
    print(f"Visit Richmond District at: {m[visit_richmond_district].as_long()} minutes past midnight")
else:
    print("No solution found")