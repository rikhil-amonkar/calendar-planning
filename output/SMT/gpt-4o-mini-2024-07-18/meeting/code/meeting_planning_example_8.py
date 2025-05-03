from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_marina = Real('depart_marina')  # Time at which we leave Chinatown to head to Marina District
arrive_marina = Real('arrive_marina')  # Time at which we arrive at Marina District
depart_stephanie = Real('depart_stephanie')  # Time we leave Marina District after meeting with Stephanie

# Constants
travel_time_chinatown_to_marina = 12  # minutes
meeting_duration = 105  # minutes
stephanie_start = 8.0     # 8:00 AM in hours
stephanie_end = 15.0       # 3:00 PM in hours
arrival_time_chinatown = 9.0  # 9:00 AM in hours

# Constraints
solver.add(arrive_marina == depart_marina + travel_time_chinatown_to_marina)
solver.add(depart_marina >= arrival_time_chinatown)  # Must leave after arriving at Chinatown
solver.add(depart_marina <= stephanie_end - meeting_duration)  # Must leave in time to meet for 105 minutes
solver.add(arrive_marina >= stephanie_start)  # Must arrive at or after Stephanie starts being available
solver.add(depart_stephanie >= arrive_marina + meeting_duration)  # Must leave after meeting for 105 minutes

# Maximize the meeting time with Stephanie (ideally want to meet her for 105 minutes)
meet_time = min(depart_stephanie - arrive_marina, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_marina_val = model[depart_marina].as_decimal(2)
    arrive_marina_val = model[arrive_marina].as_decimal(2)
    depart_stephanie_val = model[depart_stephanie].as_decimal(2)
    
    print(f"Depart from Chinatown to Marina District at: {depart_marina_val} hours")
    print(f"Arrive at Marina District at: {arrive_marina_val} hours")
    print(f"Depart from Marina District after meeting Stephanie at: {depart_stephanie_val} hours")
else:
    print("No valid schedule found.")