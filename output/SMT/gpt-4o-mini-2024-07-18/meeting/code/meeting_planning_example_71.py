from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_bayview = Real('depart_bayview')  # Time you leave Haight-Ashbury to head to Bayview
arrive_bayview = Real('arrive_bayview')  # Time you arrive at Bayview
depart_paul = Real('depart_paul')         # Time you leave Bayview after meeting Paul

# Constants
travel_time_haight_to_bayview = 18  # minutes from Haight-Ashbury to Bayview
travel_time_bayview_to_haight = 19   # minutes from Bayview back to Haight-Ashbury
meeting_duration = 90                 # minimum meeting duration (in minutes)
paul_start = 11.0                    # 11:00 AM in hours
paul_end = 16.5                      # 4:30 PM in hours
arrival_time_haight = 9.0            # 9:00 AM in hours

# Constraints
solver.add(arrive_bayview == depart_bayview + travel_time_haight_to_bayview)  # Arrival time at Bayview
solver.add(depart_bayview >= arrival_time_haight)  # Must leave after arriving at Haight-Ashbury
solver.add(depart_bayview <= paul_end - (meeting_duration / 60))  # Must leave in time to meet for 90 minutes
solver.add(arrive_bayview >= paul_start)  # Must arrive at or after Paul starts being available
solver.add(depart_paul >= arrive_bayview + (meeting_duration / 60))  # Must leave after meeting for 90 minutes

# Maximize the meeting time with Paul (ideally want to meet him for 90 minutes)
meet_time = min(depart_paul - arrive_bayview, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_bayview_val = model[depart_bayview].as_decimal(2)
    arrive_bayview_val = model[arrive_bayview].as_decimal(2)
    depart_paul_val = model[depart_paul].as_decimal(2)

    print(f"Depart from Haight-Ashbury to Bayview at: {depart_bayview_val} hours")
    print(f"Arrive at Bayview at: {arrive_bayview_val} hours")
    print(f"Depart from Bayview after meeting Paul at: {depart_paul_val} hours")
else:
    print("No valid schedule found.")