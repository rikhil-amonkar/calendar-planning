from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_nob_hill = Real('depart_nob_hill')  # Time you leave Chinatown to go to Nob Hill
arrive_nob_hill = Real('arrive_nob_hill')  # Time you arrive at Nob Hill
depart_joshua = Real('depart_joshua')       # Time you leave Nob Hill after meeting Joshua

# Constants
travel_time_chinatown_to_nob = 8  # minutes from Chinatown to Nob Hill
travel_time_nob_to_chinatown = 6    # minutes from Nob Hill to Chinatown
meeting_duration = 45               # minimum meeting duration (in minutes)
joshua_start = 10.25               # 10:15 AM in hours
joshua_end = 13.0                  # 1:00 PM in hours
arrival_time_chinatown = 9.0        # 9:00 AM in hours

# Constraints
solver.add(arrive_nob_hill == depart_nob_hill + travel_time_chinatown_to_nob)  # Arrival time at Nob Hill
solver.add(depart_nob_hill >= arrival_time_chinatown)  # Must leave after arriving at Chinatown
solver.add(depart_nob_hill <= joshua_end - (meeting_duration / 60))  # Must leave in time to meet for 45 minutes
solver.add(arrive_nob_hill >= joshua_start)  # Must arrive at or after Joshua starts being available
solver.add(depart_joshua >= arrive_nob_hill + (meeting_duration / 60))  # Must leave after meeting for 45 minutes

# Maximize the meeting time with Joshua (ideally want to meet him for 45 minutes)
meet_time = min(depart_joshua - arrive_nob_hill, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_nob_hill_val = model[depart_nob_hill].as_decimal(2)
    arrive_nob_hill_val = model[arrive_nob_hill].as_decimal(2)
    depart_joshua_val = model[depart_joshua].as_decimal(2)

    print(f"Depart from Chinatown to Nob Hill at: {depart_nob_hill_val} hours")
    print(f"Arrive at Nob Hill at: {arrive_nob_hill_val} hours")
    print(f"Depart from Nob Hill after meeting Joshua at: {depart_joshua_val} hours")
else:
    print("No valid schedule found.")