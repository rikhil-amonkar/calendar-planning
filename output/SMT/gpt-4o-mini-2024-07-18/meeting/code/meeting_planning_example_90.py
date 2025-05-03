from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_chinatown = Real('depart_chinatown')   # Time you leave Alamo Square to head to Chinatown
arrive_chinatown = Real('arrive_chinatown')   # Time you arrive at Chinatown
depart_laura = Real('depart_laura')           # Time you leave Chinatown after meeting Laura

# Constants
travel_time_alamo_to_chinatown = 16          # minutes from Alamo Square to Chinatown
travel_time_chinatown_to_alamo = 17           # minutes from Chinatown to Alamo Square
meeting_duration = 15                        # minimum meeting duration (in minutes)
laura_start = 8 + 15 / 60                   # 8:15 AM in hours
laura_end = 18 + 45 / 60                     # 6:45 PM in hours
arrival_time_alamo = 9.0                     # 9:00 AM in hours

# Constraints
solver.add(arrive_chinatown == depart_chinatown + travel_time_alamo_to_chinatown)  # Arrival time at Chinatown
solver.add(depart_chinatown >= arrival_time_alamo)  # Must leave after arriving at Alamo Square
solver.add(depart_chinatown <= laura_end - (meeting_duration / 60))  # Must leave in time to meet for 15 minutes
solver.add(arrive_chinatown >= laura_start)  # Must arrive at or after Laura starts being available
solver.add(depart_laura >= arrive_chinatown + (meeting_duration / 60))  # Must leave after meeting for 15 minutes

# Maximize the meeting time with Laura (ideally we want to meet her for at least 15 minutes)
meet_time = min(depart_laura - arrive_chinatown, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_chinatown_val = model[depart_chinatown].as_decimal(2)
    arrive_chinatown_val = model[arrive_chinatown].as_decimal(2)
    depart_laura_val = model[depart_laura].as_decimal(2)

    print(f"Depart from Alamo Square to Chinatown at: {depart_chinatown_val} hours")
    print(f"Arrive at Chinatown at: {arrive_chinatown_val} hours")
    print(f"Depart from Chinatown after meeting Laura at: {depart_laura_val} hours")
else:
    print("No valid schedule found.")