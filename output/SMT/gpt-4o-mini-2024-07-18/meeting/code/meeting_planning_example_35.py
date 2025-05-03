from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_chinatown = Real('depart_chinatown')  # Time you leave Bayview to head to Chinatown
arrive_chinatown = Real('arrive_chinatown')  # Time you arrive at Chinatown
depart_jason = Real('depart_jason')           # Time you leave Chinatown after meeting with Jason

# Constants
travel_time_bayview_to_chinatown = 18  # minutes
travel_time_chinatown_to_bayview = 22   # minutes
meeting_duration = 90                   # minutes
jason_start = 8.5                       # 8:30 AM in hours
jason_end = 12.5                        # 12:30 PM in hours
arrival_time_bayview = 9.0              # 9:00 AM in hours

# Constraints
solver.add(arrive_chinatown == depart_chinatown + travel_time_bayview_to_chinatown)
solver.add(depart_chinatown >= arrival_time_bayview)  # Must leave after arriving at Bayview
solver.add(depart_chinatown <= jason_end - meeting_duration)  # Must leave in time to meet for 90 minutes
solver.add(arrive_chinatown >= jason_start)  # Must arrive at or after Jason starts being available
solver.add(depart_jason >= arrive_chinatown + meeting_duration)  # Must leave after meeting for 90 minutes

# Maximize the meeting time with Jason (ideally want to meet him for 90 minutes)
meet_time = min(depart_jason - arrive_chinatown, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_chinatown_val = model[depart_chinatown].as_decimal(2)
    arrive_chinatown_val = model[arrive_chinatown].as_decimal(2)
    depart_jason_val = model[depart_jason].as_decimal(2)

    print(f"Depart from Bayview to Chinatown at: {depart_chinatown_val} hours")
    print(f"Arrive at Chinatown at: {arrive_chinatown_val} hours")
    print(f"Depart from Chinatown after meeting Jason at: {depart_jason_val} hours")
else:
    print("No valid schedule found.")