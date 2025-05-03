from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_mission = Real('depart_mission')  # Time you leave Financial District to head to Mission District
arrive_mission = Real('arrive_mission')  # Time you arrive at Mission District
depart_william = Real('depart_william')   # Time you leave Mission District after meeting William

# Constants
travel_time_fd_to_md = 17  # minutes from Financial District to Mission District
travel_time_md_to_fd = 17   # minutes from Mission District to Financial District
meeting_duration = 45        # minimum meeting duration (in minutes)
william_start = 13.25       # 1:15 PM in hours
william_end = 14.25         # 2:15 PM in hours
arrival_time_fd = 9.0       # 9:00 AM in hours

# Constraints
solver.add(arrive_mission == depart_mission + travel_time_fd_to_md)  # Arrival time at Mission District
solver.add(depart_mission >= arrival_time_fd)  # Must leave after arriving at Financial District
solver.add(depart_mission <= william_end - (meeting_duration / 60))  # Must leave in time to meet for 45 minutes
solver.add(arrive_mission >= william_start)  # Must arrive at or after William starts being available
solver.add(depart_william >= arrive_mission + (meeting_duration / 60))  # Must leave after meeting for 45 minutes

# Maximize the meeting time with William (ideally want to meet him for 45 minutes)
meet_time = min(depart_william - arrive_mission, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_mission_val = model[depart_mission].as_decimal(2)
    arrive_mission_val = model[arrive_mission].as_decimal(2)
    depart_william_val = model[depart_william].as_decimal(2)

    print(f"Depart from Financial District to Mission District at: {depart_mission_val} hours")
    print(f"Arrive at Mission District at: {arrive_mission_val} hours")
    print(f"Depart from Mission District after meeting William at: {depart_william_val} hours")
else:
    print("No valid schedule found.")