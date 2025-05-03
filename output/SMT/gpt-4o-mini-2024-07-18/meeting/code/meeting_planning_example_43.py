from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_chinatown = Real('depart_chinatown')  # Time you leave Marina District to head to Chinatown
arrive_chinatown = Real('arrive_chinatown')  # Time you arrive at Chinatown
depart_sandra = Real('depart_sandra')         # Time you leave Chinatown after meeting Sandra

# Constants
travel_time_marina_to_chinatown = 16  # minutes
travel_time_chinatown_to_marina = 12   # minutes
meeting_duration = 15                  # minutes
sandra_start = 9.0                     # 9:00 AM in hours
sandra_end = 11.75                     # 11:45 AM in hours
arrival_time_marina = 9.0              # 9:00 AM in hours

# Constraints
solver.add(arrive_chinatown == depart_chinatown + travel_time_marina_to_chinatown)  # Arrival time at Chinatown
solver.add(depart_chinatown >= arrival_time_marina)  # Must leave after arriving at Marina District
solver.add(depart_chinatown <= sandra_end - meeting_duration)  # Must leave in time to meet for 15 minutes
solver.add(arrive_chinatown >= sandra_start)  # Must arrive at or after Sandra starts being available
solver.add(depart_sandra >= arrive_chinatown + meeting_duration)  # Must leave after meeting for 15 minutes

# Maximize the meeting time with Sandra (ideally want to meet her for 15 minutes)
meet_time = min(depart_sandra - arrive_chinatown, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_chinatown_val = model[depart_chinatown].as_decimal(2)
    arrive_chinatown_val = model[arrive_chinatown].as_decimal(2)
    depart_sandra_val = model[depart_sandra].as_decimal(2)

    print(f"Depart from Marina District to Chinatown at: {depart_chinatown_val} hours")
    print(f"Arrive at Chinatown at: {arrive_chinatown_val} hours")
    print(f"Depart from Chinatown after meeting Sandra at: {depart_sandra_val} hours")
else:
    print("No valid schedule found.")