from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_bayview = Real('depart_bayview')  # Time you leave Presidio to head to Bayview
arrive_bayview = Real('arrive_bayview')  # Time you arrive at Bayview
depart_nancy = Real('depart_nancy')       # Time you leave Bayview after meeting Nancy

# Constants
travel_time_presidio_to_bayview = 31  # minutes from Presidio to Bayview
travel_time_bayview_to_presidio = 31   # minutes from Bayview to Presidio
meeting_duration = 30                   # minimum meeting duration (in minutes)
nancy_start = 7.25                     # 7:15 AM in hours
nancy_end = 17.5                       # 5:30 PM in hours
arrival_time_presidio = 9.0            # 9:00 AM in hours

# Constraints
solver.add(arrive_bayview == depart_bayview + travel_time_presidio_to_bayview)  # Arrival time at Bayview
solver.add(depart_bayview >= arrival_time_presidio)  # Must leave after arriving at Presidio
solver.add(depart_bayview <= nancy_end - (meeting_duration / 60))  # Must leave in time to meet for 30 minutes
solver.add(arrive_bayview >= nancy_start)  # Must arrive at or after Nancy starts being available
solver.add(depart_nancy >= arrive_bayview + (meeting_duration / 60))  # Must leave after meeting for 30 minutes

# Maximize the meeting time with Nancy (ideally want to meet her for 30 minutes)
meet_time = min(depart_nancy - arrive_bayview, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_bayview_val = model[depart_bayview].as_decimal(2)
    arrive_bayview_val = model[arrive_bayview].as_decimal(2)
    depart_nancy_val = model[depart_nancy].as_decimal(2)

    print(f"Depart from Presidio to Bayview at: {depart_bayview_val} hours")
    print(f"Arrive at Bayview at: {arrive_bayview_val} hours")
    print(f"Depart from Bayview after meeting Nancy at: {depart_nancy_val} hours")
else:
    print("No valid schedule found.")