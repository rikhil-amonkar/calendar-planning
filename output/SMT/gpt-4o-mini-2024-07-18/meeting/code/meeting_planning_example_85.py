from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_russian = Real('depart_russian')  # Time you leave North Beach to head to Russian Hill
arrive_russian = Real('arrive_russian')  # Time you arrive at Russian Hill
depart_william = Real('depart_william')   # Time you leave Russian Hill after meeting William

# Constants
travel_time_north_to_russian = 4  # minutes from North Beach to Russian Hill
travel_time_russian_to_north = 5    # minutes from Russian Hill to North Beach
meeting_duration = 15                # minimum meeting duration (in minutes)
william_start = 13.25               # 1:15 PM in hours
william_end = 21.5                  # 9:30 PM in hours
arrival_time_north = 9.0             # 9:00 AM in hours

# Constraints
solver.add(arrive_russian == depart_russian + travel_time_north_to_russian)  # Arrival time at Russian Hill
solver.add(depart_russian >= arrival_time_north)  # Must leave after arriving at North Beach
solver.add(depart_russian <= william_end - (meeting_duration / 60))  # Must leave in time to meet for 15 minutes
solver.add(arrive_russian >= william_start)  # Must arrive at or after William starts being available
solver.add(depart_william >= arrive_russian + (meeting_duration / 60))  # Must leave after meeting for 15 minutes

# Maximize the meeting time with William (ideally want to meet him for at least 15 minutes)
meet_time = min(depart_william - arrive_russian, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_russian_val = model[depart_russian].as_decimal(2)
    arrive_russian_val = model[arrive_russian].as_decimal(2)
    depart_william_val = model[depart_william].as_decimal(2)

    print(f"Depart from North Beach to Russian Hill at: {depart_russian_val} hours")
    print(f"Arrive at Russian Hill at: {arrive_russian_val} hours")
    print(f"Depart from Russian Hill after meeting William at: {depart_william_val} hours")
else:
    print("No valid schedule found.")