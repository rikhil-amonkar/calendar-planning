from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_haight = Real('depart_haight')  # Time you leave North Beach to head to Haight-Ashbury
arrive_haight = Real('arrive_haight')  # Time you arrive at Haight-Ashbury
depart_george = Real('depart_george')    # Time you leave Haight-Ashbury after meeting George

# Constants
travel_time_north_to_haight = 18  # minutes
travel_time_haight_to_north = 19   # minutes
meeting_duration = 45               # minutes
george_start = 7.5                 # 7:30 AM in hours
george_end = 13.25                 # 1:15 PM in hours
arrival_time_north = 9.0           # 9:00 AM in hours

# Constraints
solver.add(arrive_haight == depart_haight + travel_time_north_to_haight)  # Arrival time at Haight-Ashbury
solver.add(depart_haight >= arrival_time_north)  # Must leave after arriving at North Beach
solver.add(depart_haight <= george_end - meeting_duration)  # Must leave in time to meet for 45 minutes
solver.add(arrive_haight >= george_start)  # Must arrive at or after George starts being available
solver.add(depart_george >= arrive_haight + meeting_duration)  # Must leave after meeting for 45 minutes

# Maximize the meeting time with George (ideally want to meet him for 45 minutes)
meet_time = min(depart_george - arrive_haight, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_haight_val = model[depart_haight].as_decimal(2)
    arrive_haight_val = model[arrive_haight].as_decimal(2)
    depart_george_val = model[depart_george].as_decimal(2)

    print(f"Depart from North Beach to Haight-Ashbury at: {depart_haight_val} hours")
    print(f"Arrive at Haight-Ashbury at: {arrive_haight_val} hours")
    print(f"Depart from Haight-Ashbury after meeting George at: {depart_george_val} hours")
else:
    print("No valid schedule found.")