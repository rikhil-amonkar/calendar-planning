from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_chinatown = Real('depart_chinatown')  # Time you leave North Beach to head to Chinatown
arrive_chinatown = Real('arrive_chinatown')  # Time you arrive at Chinatown
depart_emily = Real('depart_emily')          # Time you leave Chinatown after meeting Emily

# Constants
travel_time_north_to_chinatown = 6          # minutes from North Beach to Chinatown
travel_time_chinatown_to_north = 3           # minutes from Chinatown to North Beach
meeting_duration = 75                         # minimum meeting duration (in minutes)
emily_start = 19.0                          # 7:00 PM in hours
emily_end = 21.0                            # 9:00 PM in hours
arrival_time_north = 9.0                      # 9:00 AM in hours

# Constraints
solver.add(arrive_chinatown == depart_chinatown + travel_time_north_to_chinatown)  # Arrival time at Chinatown
solver.add(depart_chinatown >= arrival_time_north)                                  # Must leave after arriving at North Beach
solver.add(depart_chinatown <= emily_end - (meeting_duration / 60))               # Must leave in time to meet for 75 minutes
solver.add(arrive_chinatown >= emily_start)                                        # Must arrive at or after Emily starts being available
solver.add(depart_emily >= arrive_chinatown + (meeting_duration / 60))             # Must leave after meeting for 75 minutes

# Maximize the meeting time with Emily (ideally want to meet her for at least 75 minutes)
meet_time = min(depart_emily - arrive_chinatown, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_chinatown_val = model[depart_chinatown].as_decimal(2)
    arrive_chinatown_val = model[arrive_chinatown].as_decimal(2)
    depart_emily_val = model[depart_emily].as_decimal(2)

    print(f"Depart from North Beach to Chinatown at: {depart_chinatown_val} hours")
    print(f"Arrive at Chinatown at: {arrive_chinatown_val} hours")
    print(f"Depart from Chinatown after meeting Emily at: {depart_emily_val} hours")
else:
    print("No valid schedule found.")