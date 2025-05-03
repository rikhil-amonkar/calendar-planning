from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_nob_hill = Real('depart_nob_hill')  # Time at which we leave Chinatown to head to Nob Hill
arrive_nob_hill = Real('arrive_nob_hill')  # Time at which we arrive at Nob Hill
depart_joseph = Real('depart_joseph')  # Time we leave Nob Hill after meeting with Joseph

# Constants
travel_time_chinatown_to_nob_hill = 8  # minutes
travel_time_nob_hill_to_chinatown = 6   # minutes
meeting_duration = 75                    # minutes
joseph_start = 11.5                     # 11:30 AM in hours
joseph_end = 15.25                       # 3:15 PM in hours
arrival_time_chinatown = 9.0             # 9:00 AM in hours

# Constraints
solver.add(arrive_nob_hill == depart_nob_hill + travel_time_chinatown_to_nob_hill)
solver.add(depart_nob_hill >= arrival_time_chinatown)       # Must leave after arriving at Chinatown
solver.add(depart_nob_hill <= joseph_end - meeting_duration) # Must leave in time to meet for 75 minutes
solver.add(arrive_nob_hill >= joseph_start)                 # Must arrive at or after Joseph starts being available
solver.add(depart_joseph >= arrive_nob_hill + meeting_duration)  # Must leave after meeting for 75 minutes

# Maximize the meeting time with Joseph (ideally want to meet him for 75 minutes)
meet_time = min(depart_joseph - arrive_nob_hill, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_nob_hill_val = model[depart_nob_hill].as_decimal(2)
    arrive_nob_hill_val = model[arrive_nob_hill].as_decimal(2)
    depart_joseph_val = model[depart_joseph].as_decimal(2)

    print(f"Depart from Chinatown to Nob Hill at: {depart_nob_hill_val} hours")
    print(f"Arrive at Nob Hill at: {arrive_nob_hill_val} hours")
    print(f"Depart from Nob Hill after meeting Joseph at: {depart_joseph_val} hours")
else:
    print("No valid schedule found.")