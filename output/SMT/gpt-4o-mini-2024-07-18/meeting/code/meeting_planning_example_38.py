from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_north_beach = Real('depart_north_beach')  # Time you leave Union Square to head to North Beach
arrive_north_beach = Real('arrive_north_beach')  # Time you arrive at North Beach
depart_margaret = Real('depart_margaret')         # Time you leave North Beach after meeting Margaret

# Constants
travel_time_union_to_north_beach = 10  # minutes
travel_time_north_to_union = 7          # minutes
meeting_duration = 45                    # minutes
margaret_start = 21.75                  # 9:45 PM in hours
margaret_end = 22.5                     # 10:30 PM in hours
arrival_time_union = 9.0                 # 9:00 AM in hours

# Constraints
solver.add(arrive_north_beach == depart_north_beach + travel_time_union_to_north_beach)
solver.add(depart_north_beach >= arrival_time_union)  # Must leave after arriving at Union Square
solver.add(depart_north_beach <= margaret_end - meeting_duration)  # Must leave in time to meet for 45 minutes
solver.add(arrive_north_beach >= margaret_start)  # Must arrive at or after Margaret starts being available
solver.add(depart_margaret >= arrive_north_beach + meeting_duration)  # Must leave after meeting for 45 minutes

# Maximize the meeting time with Margaret (ideally want to meet her for 45 minutes)
meet_time = min(depart_margaret - arrive_north_beach, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_north_beach_val = model[depart_north_beach].as_decimal(2)
    arrive_north_beach_val = model[arrive_north_beach].as_decimal(2)
    depart_margaret_val = model[depart_margaret].as_decimal(2)

    print(f"Depart from Union Square to North Beach at: {depart_north_beach_val} hours")
    print(f"Arrive at North Beach at: {arrive_north_beach_val} hours")
    print(f"Depart from North Beach after meeting Margaret at: {depart_margaret_val} hours")
else:
    print("No valid schedule found.")