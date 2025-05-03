from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_haight = Real('depart_haight')  # Time you leave Mission District to head to Haight-Ashbury
arrive_haight = Real('arrive_haight')  # Time you arrive at Haight-Ashbury
depart_joshua = Real('depart_joshua')   # Time you leave Haight-Ashbury after meeting Joshua

# Constants
travel_time_mission_to_haight = 12    # minutes from Mission District to Haight-Ashbury
travel_time_haight_to_mission = 11     # minutes from Haight-Ashbury to Mission District
meeting_duration = 75                   # minimum meeting duration (in minutes)
joshua_start = 11.5                    # 11:30 AM in hours
joshua_end = 22.0                      # 10:00 PM in hours
arrival_time_mission = 9.0              # 9:00 AM in hours

# Constraints
solver.add(arrive_haight == depart_haight + travel_time_mission_to_haight)  # Arrival time at Haight-Ashbury
solver.add(depart_haight >= arrival_time_mission)  # Must leave after arriving at Mission District
solver.add(depart_haight <= joshua_end - (meeting_duration / 60))  # Must leave in time to meet for 75 minutes
solver.add(arrive_haight >= joshua_start)  # Must arrive at or after Joshua starts being available
solver.add(depart_joshua >= arrive_haight + (meeting_duration / 60))  # Must leave after meeting for 75 minutes

# Maximize the meeting time with Joshua (ideally want to meet him for at least 75 minutes)
meet_time = min(depart_joshua - arrive_haight, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_haight_val = model[depart_haight].as_decimal(2)
    arrive_haight_val = model[arrive_haight].as_decimal(2)
    depart_joshua_val = model[depart_joshua].as_decimal(2)

    print(f"Depart from Mission District to Haight-Ashbury at: {depart_haight_val} hours")
    print(f"Arrive at Haight-Ashbury at: {arrive_haight_val} hours")
    print(f"Depart from Haight-Ashbury after meeting Joshua at: {depart_joshua_val} hours")
else:
    print("No valid schedule found.")