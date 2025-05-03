from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_bayview = Real('depart_bayview')  # Time you leave North Beach to head to Bayview
arrive_bayview = Real('arrive_bayview')  # Time you arrive at Bayview
depart_paul = Real('depart_paul')         # Time you leave Bayview after meeting Paul

# Constants
travel_time_north_beach_to_bayview = 22  # minutes from North Beach to Bayview
travel_time_bayview_to_north_beach = 21   # minutes from Bayview to North Beach
meeting_duration = 45                      # minimum meeting duration (in minutes)
paul_start = 13.5                         # 1:30 PM in hours
paul_end = 19.75                          # 7:45 PM in hours
arrival_time_north_beach = 9.0            # 9:00 AM in hours

# Constraints
solver.add(arrive_bayview == depart_bayview + travel_time_north_beach_to_bayview)  # Arrival time at Bayview
solver.add(depart_bayview >= arrival_time_north_beach)  # Must leave after arriving at North Beach
solver.add(depart_bayview <= paul_end - (meeting_duration / 60))  # Must leave in time to meet for 45 minutes
solver.add(arrive_bayview >= paul_start)  # Must arrive at or after Paul starts being available
solver.add(depart_paul >= arrive_bayview + (meeting_duration / 60))  # Must leave after meeting for 45 minutes

# Maximize the meeting time with Paul (ideally want to meet him for at least 45 minutes)
meet_time = min(depart_paul - arrive_bayview, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_bayview_val = model[depart_bayview].as_decimal(2)
    arrive_bayview_val = model[arrive_bayview].as_decimal(2)
    depart_paul_val = model[depart_paul].as_decimal(2)

    print(f"Depart from North Beach to Bayview at: {depart_bayview_val} hours")
    print(f"Arrive at Bayview at: {arrive_bayview_val} hours")
    print(f"Depart from Bayview after meeting Paul at: {depart_paul_val} hours")
else:
    print("No valid schedule found.")