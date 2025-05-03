from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_pacific = Real('depart_pacific')  # Time we leave Marina District to head to Pacific Heights
arrive_pacific = Real('arrive_pacific')  # Time we arrive at Pacific Heights
depart_margaret = Real('depart_margaret')  # Time we leave Pacific Heights after meeting with Margaret

# Constants
travel_time_marina_to_pacific = 7  # minutes
meeting_duration = 15                # minutes
margaret_start = 19.0               # 7:00 PM in hours
margaret_end = 19.75                # 7:45 PM in hours
arrival_time_marina = 9.0           # 9:00 AM in hours

# Constraints
solver.add(arrive_pacific == depart_pacific + travel_time_marina_to_pacific)
solver.add(depart_pacific >= arrival_time_marina)  # Must leave after arriving at Marina District
solver.add(depart_pacific <= margaret_end - meeting_duration)  # Must leave in time to meet for 15 minutes
solver.add(arrive_pacific >= margaret_start)  # Must arrive at or after Margaret starts being available
solver.add(depart_margaret >= arrive_pacific + meeting_duration)  # Must leave after meeting for 15 minutes

# Maximize the meeting time with Margaret (ideally want to meet her for 15 minutes)
meet_time = min(depart_margaret - arrive_pacific, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_pacific_val = model[depart_pacific].as_decimal(2)
    arrive_pacific_val = model[arrive_pacific].as_decimal(2)
    depart_margaret_val = model[depart_margaret].as_decimal(2)

    print(f"Depart from Marina District to Pacific Heights at: {depart_pacific_val} hours")
    print(f"Arrive at Pacific Heights at: {arrive_pacific_val} hours")
    print(f"Depart from Pacific Heights after meeting Margaret at: {depart_margaret_val} hours")
else:
    print("No valid schedule found.")