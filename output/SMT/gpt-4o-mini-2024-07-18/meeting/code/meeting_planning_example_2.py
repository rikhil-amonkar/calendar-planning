from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_sunset = Real('depart_sunset')  # Time at which we leave Haight-Ashbury to head to Sunset District
arrive_sunset = Real('arrive_sunset')  # Time at which we arrive at Sunset District
depart_jessica = Real('depart_jessica')  # Time we leave Sunset District after meeting with Jessica

# Constants
travel_time_haight_to_sunset = 15  # minutes
meeting_duration = 90  # minutes
jessica_start = 15.25  # 3:15 PM in hours
jessica_end = 20.25    # 8:15 PM in hours
arrival_time_haight = 9.0  # 9:00 AM in hours

# Constraints
solver.add(arrive_sunset == depart_sunset + travel_time_haight_to_sunset)
solver.add(depart_sunset >= arrival_time_haight)  # Must leave after arriving at Haight-Ashbury
solver.add(depart_sunset <= jessica_end - meeting_duration)  # Must leave in time to meet for 90 minutes
solver.add(arrive_sunset >= jessica_start)  # Must arrive at or after Jessica starts being available
solver.add(depart_jessica >= arrive_sunset + meeting_duration)  # Must leave after meeting for 90 minutes

# To maximize our meeting time with Jessica, we want to meet her ideally for 90 minutes
meet_time = min(depart_jessica - arrive_sunset, meeting_duration)

# We want to encourage maximization of meet_time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_sunset_val = model[depart_sunset].as_decimal(2)
    arrive_sunset_val = model[arrive_sunset].as_decimal(2)
    depart_jessica_val = model[depart_jessica].as_decimal(2)
    
    print(f"Depart from Haight-Ashbury to Sunset District at: {depart_sunset_val} hours")
    print(f"Arrive at Sunset District at: {arrive_sunset_val} hours")
    print(f"Depart from Sunset District after meeting Jessica at: {depart_jessica_val} hours")
else:
    print("No valid schedule found.")