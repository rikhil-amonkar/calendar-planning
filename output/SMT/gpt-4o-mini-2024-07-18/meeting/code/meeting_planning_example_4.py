from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_marina = Real('depart_marina')  # Time at which we leave Presidio to head to Marina District
arrive_marina = Real('arrive_marina')  # Time at which we arrive at Marina District
depart_jessica = Real('depart_jessica')  # Time we leave Marina District after meeting with Jessica

# Constants
travel_time_presidio_to_marina = 10  # minutes
meeting_duration = 60  # minutes
jessica_start = 9.25  # 9:15 AM in hours
jessica_end = 17.75    # 5:45 PM in hours
arrival_time_presidio = 9.0  # 9:00 AM in hours

# Constraints
solver.add(arrive_marina == depart_marina + travel_time_presidio_to_marina)
solver.add(depart_marina >= arrival_time_presidio)  # Must leave after arriving at Presidio
solver.add(depart_marina <= jessica_end - meeting_duration)  # Must leave in time to meet for 60 minutes
solver.add(arrive_marina >= jessica_start)  # Must arrive at or after Jessica starts being available
solver.add(depart_jessica >= arrive_marina + meeting_duration)  # Must leave after meeting for 60 minutes

# Maximize the meeting time with Jessica (ideally want to meet her for 60 minutes)
meet_time = min(depart_jessica - arrive_marina, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_marina_val = model[depart_marina].as_decimal(2)
    arrive_marina_val = model[arrive_marina].as_decimal(2)
    depart_jessica_val = model[depart_jessica].as_decimal(2)
    
    print(f"Depart from Presidio to Marina District at: {depart_marina_val} hours")
    print(f"Arrive at Marina District at: {arrive_marina_val} hours")
    print(f"Depart from Marina District after meeting Jessica at: {depart_jessica_val} hours")
else:
    print("No valid schedule found.")