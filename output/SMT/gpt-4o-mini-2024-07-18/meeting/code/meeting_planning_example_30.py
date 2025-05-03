from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_north_beach = Real('depart_north_beach')  # Time we leave Richmond District to head to North Beach
arrive_north_beach = Real('arrive_north_beach')  # Time we arrive at North Beach
depart_stephanie = Real('depart_stephanie')        # Time we leave North Beach after meeting with Stephanie

# Constants
travel_time_richmond_to_north_beach = 17  # minutes
meeting_duration = 120                     # minutes
stephanie_start = 9.5                     # 9:30 AM in hours
stephanie_end = 16.25                     # 4:15 PM in hours
arrival_time_richmond = 9.0               # 9:00 AM in hours

# Constraints
solver.add(arrive_north_beach == depart_north_beach + travel_time_richmond_to_north_beach)
solver.add(depart_north_beach >= arrival_time_richmond)  # Must leave after arriving at Richmond District
solver.add(depart_north_beach <= stephanie_end - meeting_duration)  # Must leave in time to meet for 120 minutes
solver.add(arrive_north_beach >= stephanie_start)  # Must arrive at or after Stephanie starts being available
solver.add(depart_stephanie >= arrive_north_beach + meeting_duration)  # Must leave after meeting for 120 minutes

# Maximize the meeting time with Stephanie (ideally want to meet for 120 minutes)
meet_time = min(depart_stephanie - arrive_north_beach, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_north_beach_val = model[depart_north_beach].as_decimal(2)
    arrive_north_beach_val = model[arrive_north_beach].as_decimal(2)
    depart_stephanie_val = model[depart_stephanie].as_decimal(2)

    print(f"Depart from Richmond District to North Beach at: {depart_north_beach_val} hours")
    print(f"Arrive at North Beach at: {arrive_north_beach_val} hours")
    print(f"Depart from North Beach after meeting Stephanie at: {depart_stephanie_val} hours")
else:
    print("No valid schedule found.")