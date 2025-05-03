from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_chinatown = Real('depart_chinatown')  # Time we leave Golden Gate Park to head to Chinatown
arrive_chinatown = Real('arrive_chinatown')  # Time we arrive at Chinatown
depart_david = Real('depart_david')  # Time we leave Chinatown after meeting with David

# Constants
travel_time_gg_park_to_chinatown = 23  # minutes
meeting_duration = 105                   # minutes
david_start = 16.0                       # 4:00 PM in hours
david_end = 21.75                        # 9:45 PM in hours
arrival_time_gg_park = 9.0               # 9:00 AM in hours

# Constraints
solver.add(arrive_chinatown == depart_chinatown + travel_time_gg_park_to_chinatown)
solver.add(depart_chinatown >= arrival_time_gg_park)  # Must leave after arriving at Golden Gate Park
solver.add(depart_chinatown <= david_end - meeting_duration)  # Must leave in time to meet for 105 minutes
solver.add(arrive_chinatown >= david_start)  # Must arrive at or after David starts being available
solver.add(depart_david >= arrive_chinatown + meeting_duration)  # Must leave after meeting for 105 minutes

# Maximize the meeting time with David (ideally want to meet for 105 minutes)
meet_time = min(depart_david - arrive_chinatown, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_chinatown_val = model[depart_chinatown].as_decimal(2)
    arrive_chinatown_val = model[arrive_chinatown].as_decimal(2)
    depart_david_val = model[depart_david].as_decimal(2)

    print(f"Depart from Golden Gate Park to Chinatown at: {depart_chinatown_val} hours")
    print(f"Arrive at Chinatown at: {arrive_chinatown_val} hours")
    print(f"Depart from Chinatown after meeting David at: {depart_david_val} hours")
else:
    print("No valid schedule found.")