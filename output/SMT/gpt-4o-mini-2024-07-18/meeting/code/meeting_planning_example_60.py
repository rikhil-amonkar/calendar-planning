from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_chinatown = Real('depart_chinatown')  # Time you leave Union Square to head to Chinatown
arrive_chinatown = Real('arrive_chinatown')  # Time you arrive at Chinatown
depart_carol = Real('depart_carol')           # Time you leave Chinatown after meeting Carol

# Constants
travel_time_us_to_chinatown = 7  # minutes from Union Square to Chinatown
travel_time_chinatown_to_us = 7   # minutes from Chinatown to Union Square
meeting_duration = 45              # minimum meeting duration (in minutes)
carol_start = 18.5                # 6:30 PM in hours
carol_end = 20.0                  # 8:00 PM in hours
arrival_time_us = 9.0             # 9:00 AM in hours

# Constraints
solver.add(arrive_chinatown == depart_chinatown + travel_time_us_to_chinatown)  # Arrival time at Chinatown
solver.add(depart_chinatown >= arrival_time_us)  # Must leave after arriving at Union Square
solver.add(depart_chinatown <= carol_end - (meeting_duration / 60))  # Must leave in time to meet for 45 minutes
solver.add(arrive_chinatown >= carol_start)  # Must arrive at or after Carol starts being available
solver.add(depart_carol >= arrive_chinatown + (meeting_duration / 60))  # Must leave after meeting for 45 minutes

# Maximize the meeting time with Carol (ideally want to meet her for 45 minutes)
meet_time = min(depart_carol - arrive_chinatown, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_chinatown_val = model[depart_chinatown].as_decimal(2)
    arrive_chinatown_val = model[arrive_chinatown].as_decimal(2)
    depart_carol_val = model[depart_carol].as_decimal(2)

    print(f"Depart from Union Square to Chinatown at: {depart_chinatown_val} hours")
    print(f"Arrive at Chinatown at: {arrive_chinatown_val} hours")
    print(f"Depart from Chinatown after meeting Carol at: {depart_carol_val} hours")
else:
    print("No valid schedule found.")