from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_nob_hill = Real('depart_nob_hill')  # Time at which we leave Union Square to head to Nob Hill
arrive_nob_hill = Real('arrive_nob_hill')  # Time at which we arrive at Nob Hill
depart_mary = Real('depart_mary')  # Time we leave Nob Hill after meeting with Mary

# Constants
travel_time_union_to_nob = 9  # minutes
travel_time_nob_to_union = 7   # minutes
meeting_duration = 75  # minutes
mary_start = 12.0      # 12:00 PM in hours
mary_end = 16.25       # 4:15 PM in hours
arrival_time_union = 9.0  # 9:00 AM in hours

# Constraints
solver.add(arrive_nob_hill == depart_nob_hill + travel_time_union_to_nob)
solver.add(depart_nob_hill >= arrival_time_union)  # Must leave after arriving at Union Square
solver.add(depart_nob_hill <= mary_end - meeting_duration)  # Must leave in time to meet for 75 minutes
solver.add(arrive_nob_hill >= mary_start)  # Must arrive at or after Mary starts being available
solver.add(depart_mary >= arrive_nob_hill + meeting_duration)  # Must leave after meeting for 75 minutes

# Maximize the meeting time with Mary (ideally want to meet her for 75 minutes)
meet_time = min(depart_mary - arrive_nob_hill, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_nob_hill_val = model[depart_nob_hill].as_decimal(2)
    arrive_nob_hill_val = model[arrive_nob_hill].as_decimal(2)
    depart_mary_val = model[depart_mary].as_decimal(2)
    
    print(f"Depart from Union Square to Nob Hill at: {depart_nob_hill_val} hours")
    print(f"Arrive at Nob Hill at: {arrive_nob_hill_val} hours")
    print(f"Depart from Nob Hill after meeting Mary at: {depart_mary_val} hours")
else:
    print("No valid schedule found.")