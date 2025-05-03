from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_alamo = Real('depart_alamo')  # Time we leave Nob Hill to head to Alamo Square
arrive_alamo = Real('arrive_alamo')  # Time we arrive at Alamo Square
depart_anthony = Real('depart_anthony')  # Time we leave Alamo Square after meeting Anthony

# Constants
travel_time_nob_hill_to_alamo = 11  # minutes
meeting_duration = 15                 # minutes
anthony_start = 7.25                  # 7:15 AM in hours
anthony_end = 13.0                    # 1:00 PM in hours
arrival_time_nob_hill = 9.0           # 9:00 AM in hours

# Constraints
solver.add(arrive_alamo == depart_alamo + travel_time_nob_hill_to_alamo)
solver.add(depart_alamo >= arrival_time_nob_hill)  # Must leave after arriving at Nob Hill
solver.add(depart_alamo <= anthony_end - meeting_duration)  # Must leave in time to meet for 15 minutes
solver.add(arrive_alamo >= anthony_start)  # Must arrive at or after Anthony starts being available
solver.add(depart_anthony >= arrive_alamo + meeting_duration)  # Must leave after meeting for 15 minutes

# Maximize the meeting time with Anthony (ideally want to meet him for 15 minutes)
meet_time = min(depart_anthony - arrive_alamo, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_alamo_val = model[depart_alamo].as_decimal(2)
    arrive_alamo_val = model[arrive_alamo].as_decimal(2)
    depart_anthony_val = model[depart_anthony].as_decimal(2)

    print(f"Depart from Nob Hill to Alamo Square at: {depart_alamo_val} hours")
    print(f"Arrive at Alamo Square at: {arrive_alamo_val} hours")
    print(f"Depart from Alamo Square after meeting Anthony at: {depart_anthony_val} hours")
else:
    print("No valid schedule found.")