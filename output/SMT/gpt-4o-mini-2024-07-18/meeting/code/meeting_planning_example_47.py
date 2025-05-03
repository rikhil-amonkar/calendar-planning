from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_nob_hill = Real('depart_nob_hill')  # Time you leave Richmond District to head to Nob Hill
arrive_nob_hill = Real('arrive_nob_hill')  # Time you arrive at Nob Hill
depart_paul = Real('depart_paul')           # Time you leave Nob Hill after meeting Paul

# Constants
travel_time_richmond_to_nob = 17  # minutes from Richmond District to Nob Hill
travel_time_nob_to_richmond = 14   # minutes from Nob Hill back to Richmond District
meeting_duration = 15               # minimum meeting duration (in minutes)
paul_start = 9.5                   # 9:30 AM in hours
paul_end = 11.25                   # 11:15 AM in hours
arrival_time_richmond = 9.0        # 9:00 AM in hours

# Constraints
solver.add(arrive_nob_hill == depart_nob_hill + travel_time_richmond_to_nob)  # Arrival time at Nob Hill
solver.add(depart_nob_hill >= arrival_time_richmond)  # Must leave after arriving at Richmond District
solver.add(depart_nob_hill <= paul_end - meeting_duration)  # Must leave in time to meet for 15 minutes
solver.add(arrive_nob_hill >= paul_start)  # Must arrive at or after Paul starts being available
solver.add(depart_paul >= arrive_nob_hill + meeting_duration)  # Must leave after meeting for 15 minutes

# Maximize the meeting time with Paul (ideally want to meet him for 15 minutes)
meet_time = min(depart_paul - arrive_nob_hill, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_nob_hill_val = model[depart_nob_hill].as_decimal(2)
    arrive_nob_hill_val = model[arrive_nob_hill].as_decimal(2)
    depart_paul_val = model[depart_paul].as_decimal(2)

    print(f"Depart from Richmond District to Nob Hill at: {depart_nob_hill_val} hours")
    print(f"Arrive at Nob Hill at: {arrive_nob_hill_val} hours")
    print(f"Depart from Nob Hill after meeting Paul at: {depart_paul_val} hours")
else:
    print("No valid schedule found.")