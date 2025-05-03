from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_richmond = Real('depart_richmond')  # Time at which we leave Marina District to head to Richmond District
arrive_richmond = Real('arrive_richmond')  # Time at which we arrive at Richmond District
depart_betty = Real('depart_betty')  # Time we leave Richmond District after meeting with Betty

# Constants
travel_time_marina_to_richmond = 11  # minutes
meeting_duration = 75                  # minutes
betty_start = 20.5                     # 8:30 PM in hours
betty_end = 22.0                       # 10:00 PM in hours
arrival_time_marina = 9.0              # 9:00 AM in hours

# Constraints
solver.add(arrive_richmond == depart_richmond + travel_time_marina_to_richmond)
solver.add(depart_richmond >= arrival_time_marina)  # Must leave after arriving at Marina District
solver.add(depart_richmond <= betty_end - meeting_duration)  # Must leave in time to meet for 75 minutes
solver.add(arrive_richmond >= betty_start)  # Must arrive at or after Betty starts being available
solver.add(depart_betty >= arrive_richmond + meeting_duration)  # Must leave after meeting for 75 minutes

# Maximize the meeting time with Betty (ideally want to meet her for 75 minutes)
meet_time = min(depart_betty - arrive_richmond, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_richmond_val = model[depart_richmond].as_decimal(2)
    arrive_richmond_val = model[arrive_richmond].as_decimal(2)
    depart_betty_val = model[depart_betty].as_decimal(2)

    print(f"Depart from Marina District to Richmond District at: {depart_richmond_val} hours")
    print(f"Arrive at Richmond District at: {arrive_richmond_val} hours")
    print(f"Depart from Richmond District after meeting Betty at: {depart_betty_val} hours")
else:
    print("No valid schedule found.")