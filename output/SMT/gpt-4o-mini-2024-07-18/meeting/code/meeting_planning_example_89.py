from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_bayview = Real('depart_bayview')  # Time you leave Mission District to head to Bayview
arrive_bayview = Real('arrive_bayview')  # Time you arrive at Bayview
depart_patricia = Real('depart_patricia') # Time you leave Bayview after meeting Patricia

# Constants
travel_time_mission_to_bayview = 15    # minutes from Mission District to Bayview
travel_time_bayview_to_mission = 13     # minutes from Bayview to Mission District
meeting_duration = 60                    # minimum meeting duration (in minutes)
patricia_start = 18.0                   # 6:00 PM in hours
patricia_end = 19.5                      # 7:30 PM in hours
arrival_time_mission = 9.0               # 9:00 AM in hours

# Constraints
solver.add(arrive_bayview == depart_bayview + travel_time_mission_to_bayview)  # Arrival time at Bayview
solver.add(depart_bayview >= arrival_time_mission)  # Must leave after arriving at Mission District
solver.add(depart_bayview <= patricia_end - (meeting_duration / 60))  # Must leave in time to meet for 60 minutes
solver.add(arrive_bayview >= patricia_start)  # Must arrive at or after Patricia starts being available
solver.add(depart_patricia >= arrive_bayview + (meeting_duration / 60))  # Must leave after meeting for 60 minutes

# Maximize the meeting time with Patricia (ideally want to meet her for at least 60 minutes)
meet_time = min(depart_patricia - arrive_bayview, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_bayview_val = model[depart_bayview].as_decimal(2)
    arrive_bayview_val = model[arrive_bayview].as_decimal(2)
    depart_patricia_val = model[depart_patricia].as_decimal(2)

    print(f"Depart from Mission District to Bayview at: {depart_bayview_val} hours")
    print(f"Arrive at Bayview at: {arrive_bayview_val} hours")
    print(f"Depart from Bayview after meeting Patricia at: {depart_patricia_val} hours")
else:
    print("No valid schedule found.")