from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_bayview = Real('depart_bayview')  # Time you leave Richmond District to head to Bayview
arrive_bayview = Real('arrive_bayview')  # Time you arrive at Bayview
depart_sarah = Real('depart_sarah')       # Time you leave Bayview after meeting Sarah

# Constants
travel_time_richmond_to_bayview = 26  # minutes from Richmond District to Bayview
travel_time_bayview_to_richmond = 25   # minutes from Bayview to Richmond District
meeting_duration = 45                   # minimum meeting duration (in minutes)
sarah_start = 14.25                     # 2:15 PM in hours
sarah_end = 17.5                        # 5:30 PM in hours
arrival_time_richmond = 9.0             # 9:00 AM in hours

# Constraints
solver.add(arrive_bayview == depart_bayview + travel_time_richmond_to_bayview)  # Arrival time at Bayview
solver.add(depart_bayview >= arrival_time_richmond)  # Must leave after arriving at Richmond District
solver.add(depart_bayview <= sarah_end - meeting_duration)  # Must leave in time to meet for 45 minutes
solver.add(arrive_bayview >= sarah_start)  # Must arrive at or after Sarah starts being available
solver.add(depart_sarah >= arrive_bayview + meeting_duration)  # Must leave after meeting for 45 minutes

# Maximize the meeting time with Sarah (ideally want to meet her for 45 minutes)
meet_time = min(depart_sarah - arrive_bayview, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_bayview_val = model[depart_bayview].as_decimal(2)
    arrive_bayview_val = model[arrive_bayview].as_decimal(2)
    depart_sarah_val = model[depart_sarah].as_decimal(2)

    print(f"Depart from Richmond District to Bayview at: {depart_bayview_val} hours")
    print(f"Arrive at Bayview at: {arrive_bayview_val} hours")
    print(f"Depart from Bayview after meeting Sarah at: {depart_sarah_val} hours")
else:
    print("No valid schedule found.")