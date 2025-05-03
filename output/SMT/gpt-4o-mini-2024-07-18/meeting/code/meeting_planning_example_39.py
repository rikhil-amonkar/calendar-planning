from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_nob_hill = Real('depart_nob_hill')  # Time you leave Fisherman's Wharf to head to Nob Hill
arrive_nob_hill = Real('arrive_nob_hill')  # Time you arrive at Nob Hill
depart_stephanie = Real('depart_stephanie')  # Time you leave Nob Hill after meeting with Stephanie

# Constants
travel_time_wharf_to_nob = 11  # minutes
meeting_duration = 120           # minutes
stephanie_start = 16.75         # 4:45 PM in hours
stephanie_end = 21.75           # 9:45 PM in hours
arrival_time_wharf = 9.0        # 9:00 AM in hours

# Constraints
solver.add(arrive_nob_hill == depart_nob_hill + travel_time_wharf_to_nob)  # Arrival time at Nob Hill
solver.add(depart_nob_hill >= arrival_time_wharf)  # Must leave after arriving at Fisherman's Wharf
solver.add(depart_nob_hill <= stephanie_end - meeting_duration)  # Must leave in time to meet for 120 minutes
solver.add(arrive_nob_hill >= stephanie_start)  # Must arrive at or after Stephanie starts being available
solver.add(depart_stephanie >= arrive_nob_hill + meeting_duration)  # Must leave after meeting for 120 minutes

# Maximize the meeting time with Stephanie (ideally want to meet her for 120 minutes)
meet_time = min(depart_stephanie - arrive_nob_hill, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_nob_hill_val = model[depart_nob_hill].as_decimal(2)
    arrive_nob_hill_val = model[arrive_nob_hill].as_decimal(2)
    depart_stephanie_val = model[depart_stephanie].as_decimal(2)

    print(f"Depart from Fisherman's Wharf to Nob Hill at: {depart_nob_hill_val} hours")
    print(f"Arrive at Nob Hill at: {arrive_nob_hill_val} hours")
    print(f"Depart from Nob Hill after meeting Stephanie at: {depart_stephanie_val} hours")
else:
    print("No valid schedule found.")