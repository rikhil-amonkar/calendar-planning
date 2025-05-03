from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_bayview = Real('depart_bayview')  # Time you leave North Beach to head to Bayview
arrive_bayview = Real('arrive_bayview')  # Time you arrive at Bayview
depart_steven = Real('depart_steven')     # Time you leave Bayview after meeting Steven

# Constants
travel_time_north_to_bayview = 22        # minutes from North Beach to Bayview
travel_time_bayview_to_north = 21         # minutes from Bayview to North Beach
meeting_duration = 90                      # minimum meeting duration (in minutes)
steven_start = 11.0                       # 11:00 AM in hours
steven_end = 12.75                        # 12:45 PM in hours
arrival_time_north = 9.0                  # 9:00 AM in hours

# Constraints
solver.add(arrive_bayview == depart_bayview + travel_time_north_to_bayview)  # Arrival time at Bayview
solver.add(depart_bayview >= arrival_time_north)  # Must leave after arriving at North Beach
solver.add(depart_bayview <= steven_end - (meeting_duration / 60))  # Must leave in time to meet for 90 minutes
solver.add(arrive_bayview >= steven_start)  # Must arrive at or after Steven starts being available
solver.add(depart_steven >= arrive_bayview + (meeting_duration / 60))  # Must leave after meeting for 90 minutes

# Maximize the meeting time with Steven (ideally we want to meet him for at least 90 minutes)
meet_time = min(depart_steven - arrive_bayview, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_bayview_val = model[depart_bayview].as_decimal(2)
    arrive_bayview_val = model[arrive_bayview].as_decimal(2)
    depart_steven_val = model[depart_steven].as_decimal(2)

    print(f"Depart from North Beach to Bayview at: {depart_bayview_val} hours")
    print(f"Arrive at Bayview at: {arrive_bayview_val} hours")
    print(f"Depart from Bayview after meeting Steven at: {depart_steven_val} hours")
else:
    print("No valid schedule found.")