from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_north_beach = Real('depart_north_beach')  # Time at which we leave Presidio to head to North Beach
arrive_north_beach = Real('arrive_north_beach')  # Time at which we arrive at North Beach
depart_betty = Real('depart_betty')  # Time we leave North Beach after meeting with Betty

# Constants
travel_time_presidio_to_north_beach = 18  # minutes
meeting_duration = 75  # minutes
betty_start = 18.75    # 6:45 PM in hours
betty_end = 22.0       # 10:00 PM in hours
arrival_time_presidio = 9.0  # 9:00 AM in hours

# Constraints
solver.add(arrive_north_beach == depart_north_beach + travel_time_presidio_to_north_beach)
solver.add(depart_north_beach >= arrival_time_presidio)  # Must leave after arriving at Presidio
solver.add(depart_north_beach <= betty_end - meeting_duration)  # Must leave in time to meet for 75 minutes
solver.add(arrive_north_beach >= betty_start)  # Must arrive at or after Betty starts being available
solver.add(depart_betty >= arrive_north_beach + meeting_duration)  # Must leave after meeting for 75 minutes

# Maximize the meeting time with Betty (ideally want to meet her for 75 minutes)
meet_time = min(depart_betty - arrive_north_beach, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_north_beach_val = model[depart_north_beach].as_decimal(2)
    arrive_north_beach_val = model[arrive_north_beach].as_decimal(2)
    depart_betty_val = model[depart_betty].as_decimal(2)

    print(f"Depart from Presidio to North Beach at: {depart_north_beach_val} hours")
    print(f"Arrive at North Beach at: {arrive_north_beach_val} hours")
    print(f"Depart from North Beach after meeting Betty at: {depart_betty_val} hours")
else:
    print("No valid schedule found.")