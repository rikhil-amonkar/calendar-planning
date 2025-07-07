from z3 import *

# Define the time variables
arrival_time = 9 * 60  # 9:00 AM in minutes
timothy_start = 20 * 60 + 45  # 8:45 PM in minutes
timothy_end = 20 * 60 + 90  # 9:30 PM in minutes
min_meeting_duration = 45  # Minimum meeting duration in minutes

# Create a solver instance
solver = Solver()

# Define the visit times for each location
visit_richmond_district = Int('visit_richmond_district')

# Constraints
# You start at Alamo Square at 9:00 AM
# Travel time to Richmond District is 12 minutes
# Travel time back to Alamo Square is 13 minutes
# You need to meet Timothy for exactly 45 minutes between 8:45 PM and 9:30 PM

# Ensure you arrive at Richmond District before 8:45 PM and leave by 9:30 PM
solver.add(visit_richmond_district >= arrival_time + 12)  # Arrive at Richmond District after traveling
solver.add(visit_richmond_district + min_meeting_duration + 13 <= timothy_end)  # Leave Alamo Square after meeting

# Meeting Timothy constraint
# You need to meet Timothy for exactly 45 minutes between 8:45 PM and 9:30 PM
solver.add(visit_richmond_district == timothy_start)
solver.add(visit_richmond_district + min_meeting_duration == timothy_end)

# Check if the problem is solvable
if solver.check() == sat:
    m = solver.model()
    print("SOLUTION:")
    print(f"Visit Alamo Square at: {arrival_time} minutes past midnight (9:00 AM)")
    print(f"Travel to Richmond District at: {arrival_time + 12} minutes past midnight (9:12 AM)")
    print(f"Visit Richmond District at: {m[visit_richmond_district].as_long()} minutes past midnight (8:45 PM)")
    print(f"Leave Richmond District at: {m[visit_richmond_district].as_long() + min_meeting_duration} minutes past midnight (9:30 PM)")
    print(f"Return to Alamo Square at: {m[visit_richmond_district].as_long() + min_meeting_duration + 13} minutes past midnight (9:43 PM)")
else:
    print("No solution found")