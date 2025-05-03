from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_chinatown = Real('depart_chinatown')  # Time we leave Union Square to head to Chinatown
arrive_chinatown = Real('arrive_chinatown')  # Time we arrive at Chinatown
depart_joshua = Real('depart_joshua')        # Time we leave Chinatown after meeting with Joshua

# Constants
travel_time_union_to_chinatown = 7  # minutes
meeting_duration = 75                # minutes
joshua_start = 18.0                 # 6:00 PM in hours
joshua_end = 21.5                   # 9:30 PM in hours
arrival_time_union = 9.0             # 9:00 AM in hours

# Constraints
solver.add(arrive_chinatown == depart_chinatown + travel_time_union_to_chinatown)
solver.add(depart_chinatown >= arrival_time_union)  # Must leave after arriving at Union Square
solver.add(depart_chinatown <= joshua_end - meeting_duration)  # Must leave in time to meet for 75 minutes
solver.add(arrive_chinatown >= joshua_start)  # Must arrive at or after Joshua starts being available
solver.add(depart_joshua >= arrive_chinatown + meeting_duration)  # Must leave after meeting for 75 minutes

# Maximize the meeting time with Joshua (ideally want to meet for 75 minutes)
meet_time = min(depart_joshua - arrive_chinatown, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_chinatown_val = model[depart_chinatown].as_decimal(2)
    arrive_chinatown_val = model[arrive_chinatown].as_decimal(2)
    depart_joshua_val = model[depart_joshua].as_decimal(2)

    print(f"Depart from Union Square to Chinatown at: {depart_chinatown_val} hours")
    print(f"Arrive at Chinatown at: {arrive_chinatown_val} hours")
    print(f"Depart from Chinatown after meeting Joshua at: {depart_joshua_val} hours")
else:
    print("No valid schedule found.")