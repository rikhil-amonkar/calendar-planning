from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_mission = Real('depart_mission')  # Time at which we leave Marina District to head to Mission District
arrive_mission = Real('arrive_mission')  # Time at which we arrive at Mission District
depart_stephanie = Real('depart_stephanie')  # Time after the meeting with Stephanie when we leave Mission District

# Constants
travel_time_marina_to_mission = 20  # minutes
meeting_duration = 120  # minutes
stephanie_start = 10.5  # 10:30 AM in hours
stephanie_end = 13.5  # 1:30 PM in hours
arrival_time_marina = 9.0  # 9:00 AM in hours

# Constraints
solver.add(arrive_mission == depart_mission + travel_time_marina_to_mission)
solver.add(depart_mission >= arrival_time_marina)  # Must leave after arriving at Marina
solver.add(depart_mission <= stephanie_end - meeting_duration)  # Must leave by this time to meet for 120 minutes
solver.add(arrive_mission >= stephanie_start)  # Must arrive at or after Stephanie starts being available
solver.add(depart_stephanie >= arrive_mission + meeting_duration)  # Must leave after meeting for 120 minutes

# To maximize our meeting time with Stephanie, we want to meet her until the end of her availability
# If we meet her for 120 minutes:
# (i.e., We should not depart before meeting for the full duration)
meet_time = min(depart_stephanie - arrive_mission, meeting_duration)

# We want to encourage as much meet_time as possible
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_mission_val = model[depart_mission].as_decimal(2)
    arrive_mission_val = model[arrive_mission].as_decimal(2)
    depart_stephanie_val = model[depart_stephanie].as_decimal(2)
    
    print(f"Depart from Marina District to Mission District at: {depart_mission_val} hours")
    print(f"Arrive at Mission District at: {arrive_mission_val} hours")
    print(f"Depart from Mission District after meeting Stephanie at: {depart_stephanie_val} hours")
else:
    print("No valid schedule found.")