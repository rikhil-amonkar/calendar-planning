from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_sunset = Real('depart_sunset')  # Time at which we leave Nob Hill to head to Sunset District
arrive_sunset = Real('arrive_sunset')  # Time at which we arrive at Sunset District
depart_carol = Real('depart_carol')  # Time we leave Sunset District after meeting with Carol

# Constants
travel_time_nobhill_to_sunset = 25  # minutes
meeting_duration = 75  # minutes
carol_start = 14.0      # 2:00 PM in hours
carol_end = 20.5        # 8:30 PM in hours
arrival_time_nobhill = 9.0  # 9:00 AM in hours

# Constraints
solver.add(arrive_sunset == depart_sunset + travel_time_nobhill_to_sunset)
solver.add(depart_sunset >= arrival_time_nobhill)  # Must leave after arriving at Nob Hill
solver.add(depart_sunset <= carol_end - meeting_duration)  # Must leave in time to meet for 75 minutes
solver.add(arrive_sunset >= carol_start)  # Must arrive at or after Carol starts being available
solver.add(depart_carol >= arrive_sunset + meeting_duration)  # Must leave after meeting for 75 minutes

# Maximize the meeting time with Carol (ideally want to meet her for 75 minutes)
meet_time = min(depart_carol - arrive_sunset, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_sunset_val = model[depart_sunset].as_decimal(2)
    arrive_sunset_val = model[arrive_sunset].as_decimal(2)
    depart_carol_val = model[depart_carol].as_decimal(2)
    
    print(f"Depart from Nob Hill to Sunset District at: {depart_sunset_val} hours")
    print(f"Arrive at Sunset District at: {arrive_sunset_val} hours")
    print(f"Depart from Sunset District after meeting Carol at: {depart_carol_val} hours")
else:
    print("No valid schedule found.")