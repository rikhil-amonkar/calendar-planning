from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_haight = Real('depart_haight')  # Time at which we leave Mission District to head to Haight-Ashbury
arrive_haight = Real('arrive_haight')  # Time at which we arrive at Haight-Ashbury
depart_margaret = Real('depart_margaret')  # Time we leave Haight-Ashbury after meeting with Margaret

# Constants
travel_time_mission_to_haight = 12  # minutes
meeting_duration = 30                 # minutes
margaret_start = 8.0                 # 8:00 AM in hours
margaret_end = 15.75                  # 3:45 PM in hours
arrival_time_mission = 9.0            # 9:00 AM in hours

# Constraints
solver.add(arrive_haight == depart_haight + travel_time_mission_to_haight)
solver.add(depart_haight >= arrival_time_mission)                # Must leave after arriving at Mission District
solver.add(depart_haight <= margaret_end - meeting_duration)     # Must leave in time to meet for 30 minutes
solver.add(arrive_haight >= margaret_start)                      # Must arrive at or after Margaret starts being available
solver.add(depart_margaret >= arrive_haight + meeting_duration)  # Must leave after meeting for 30 minutes

# Maximize the meeting time with Margaret (ideally want to meet her for 30 minutes)
meet_time = min(depart_margaret - arrive_haight, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_haight_val = model[depart_haight].as_decimal(2)
    arrive_haight_val = model[arrive_haight].as_decimal(2)
    depart_margaret_val = model[depart_margaret].as_decimal(2)

    print(f"Depart from Mission District to Haight-Ashbury at: {depart_haight_val} hours")
    print(f"Arrive at Haight-Ashbury at: {arrive_haight_val} hours")
    print(f"Depart from Haight-Ashbury after meeting Margaret at: {depart_margaret_val} hours")
else:
    print("No valid schedule found.")