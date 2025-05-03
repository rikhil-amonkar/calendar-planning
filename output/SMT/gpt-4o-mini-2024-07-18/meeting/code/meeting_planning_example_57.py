from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_sunset = Real('depart_sunset')  # Time you leave Bayview to head to Sunset District
arrive_sunset = Real('arrive_sunset')  # Time you arrive at Sunset District
depart_jessica = Real('depart_jessica')  # Time you leave Sunset District after meeting Jessica

# Constants
travel_time_bayview_to_sunset = 23  # minutes from Bayview to Sunset District
travel_time_sunset_to_bayview = 22    # minutes from Sunset District to Bayview
meeting_duration = 60                 # minimum meeting duration (in minutes)
jessica_start = 10.5                 # 10:30 AM in hours
jessica_end = 17.75                   # 5:45 PM in hours
arrival_time_bayview = 9.0            # 9:00 AM in hours

# Constraints
solver.add(arrive_sunset == depart_sunset + travel_time_bayview_to_sunset)  # Arrival time at Sunset District
solver.add(depart_sunset >= arrival_time_bayview)  # Must leave after arriving at Bayview
solver.add(depart_sunset <= jessica_end - (meeting_duration / 60))  # Must leave in time to meet for 60 minutes
solver.add(arrive_sunset >= jessica_start)  # Must arrive at or after Jessica starts being available
solver.add(depart_jessica >= arrive_sunset + (meeting_duration / 60))  # Must leave after meeting for 60 minutes

# Maximize the meeting time with Jessica (ideally want to meet her for 60 minutes)
meet_time = min(depart_jessica - arrive_sunset, meeting_duration / 60)

# We want to maximize the meeting duration
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_sunset_val = model[depart_sunset].as_decimal(2)
    arrive_sunset_val = model[arrive_sunset].as_decimal(2)
    depart_jessica_val = model[depart_jessica].as_decimal(2)

    print(f"Depart from Bayview to Sunset District at: {depart_sunset_val} hours")
    print(f"Arrive at Sunset District at: {arrive_sunset_val} hours")
    print(f"Depart from Sunset District after meeting Jessica at: {depart_jessica_val} hours")
else:
    print("No valid schedule found.")