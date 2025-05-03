from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_nob_hill = Real('depart_nob_hill')  # Time at which we leave Fisherman's Wharf to head to Nob Hill
arrive_nob_hill = Real('arrive_nob_hill')  # Time at which we arrive at Nob Hill
depart_kenneth = Real('depart_kenneth')  # Time we leave Nob Hill after meeting with Kenneth

# Constants
travel_time_wharf_to_nob_hill = 11  # minutes
meeting_duration = 90  # minutes
kenneth_start = 14.25  # 2:15 PM in hours
kenneth_end = 19.75   # 7:45 PM in hours
arrival_time_wharf = 9.0  # 9:00 AM in hours

# Constraints
solver.add(arrive_nob_hill == depart_nob_hill + travel_time_wharf_to_nob_hill)
solver.add(depart_nob_hill >= arrival_time_wharf)  # Must leave after arriving at Fisherman's Wharf
solver.add(depart_nob_hill <= kenneth_end - meeting_duration)  # Must leave in time to meet for 90 minutes
solver.add(arrive_nob_hill >= kenneth_start)  # Must arrive at or after Kenneth starts being available
solver.add(depart_kenneth >= arrive_nob_hill + meeting_duration)  # Must leave after meeting for 90 minutes

# Maximize the meeting time with Kenneth (ideally want to meet him for 90 minutes)
meet_time = min(depart_kenneth - arrive_nob_hill, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_nob_hill_val = model[depart_nob_hill].as_decimal(2)
    arrive_nob_hill_val = model[arrive_nob_hill].as_decimal(2)
    depart_kenneth_val = model[depart_kenneth].as_decimal(2)
    
    print(f"Depart from Fisherman's Wharf to Nob Hill at: {depart_nob_hill_val} hours")
    print(f"Arrive at Nob Hill at: {arrive_nob_hill_val} hours")
    print(f"Depart from Nob Hill after meeting Kenneth at: {depart_kenneth_val} hours")
else:
    print("No valid schedule found.")