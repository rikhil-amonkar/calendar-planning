from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_north_beach = Real('depart_north_beach')  # Time you leave Haight-Ashbury to head to North Beach
arrive_north_beach = Real('arrive_north_beach')  # Time you arrive at North Beach
depart_robert = Real('depart_robert')              # Time you leave North Beach after meeting Robert

# Constants
travel_time_haight_to_north = 19  # minutes from Haight-Ashbury to North Beach
travel_time_north_to_haight = 18   # minutes from North Beach to Haight-Ashbury
meeting_duration = 90               # minutes
robert_start = 16.5                # 4:30 PM in hours
robert_end = 21.5                  # 9:30 PM in hours
arrival_time_haight = 9.0          # 9:00 AM in hours

# Constraints
solver.add(arrive_north_beach == depart_north_beach + travel_time_haight_to_north)  # Arrival time at North Beach
solver.add(depart_north_beach >= arrival_time_haight)  # Must leave after arriving at Haight-Ashbury
solver.add(depart_north_beach <= robert_end - meeting_duration)  # Must leave in time to meet for 90 minutes
solver.add(arrive_north_beach >= robert_start)  # Must arrive at or after Robert starts being available
solver.add(depart_robert >= arrive_north_beach + meeting_duration)  # Must leave after meeting for 90 minutes

# Maximize the meeting time with Robert (ideally want to meet him for 90 minutes)
meet_time = min(depart_robert - arrive_north_beach, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_north_beach_val = model[depart_north_beach].as_decimal(2)
    arrive_north_beach_val = model[arrive_north_beach].as_decimal(2)
    depart_robert_val = model[depart_robert].as_decimal(2)

    print(f"Depart from Haight-Ashbury to North Beach at: {depart_north_beach_val} hours")
    print(f"Arrive at North Beach at: {arrive_north_beach_val} hours")
    print(f"Depart from North Beach after meeting Robert at: {depart_robert_val} hours")
else:
    print("No valid schedule found.")