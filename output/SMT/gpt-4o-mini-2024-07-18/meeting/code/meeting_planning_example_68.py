from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_russian = Real('depart_russian')  # Time you leave Haight-Ashbury to head to Russian Hill
arrive_russian = Real('arrive_russian')  # Time you arrive at Russian Hill
depart_patricia = Real('depart_patricia')  # Time you leave Russian Hill after meeting Patricia

# Constants
travel_time_haight_to_russian = 17  # minutes from Haight-Ashbury to Russian Hill
travel_time_russian_to_haight = 17   # minutes from Russian Hill to Haight-Ashbury
meeting_duration = 30                 # minimum meeting duration (in minutes)
patricia_start = 7.75                 # 7:45 AM in hours
patricia_end = 14.25                  # 2:15 PM in hours
arrival_time_haight = 9.0             # 9:00 AM in hours

# Constraints
solver.add(arrive_russian == depart_russian + travel_time_haight_to_russian)  # Calculate arrival time at Russian Hill
solver.add(depart_russian >= arrival_time_haight)  # Must leave after arriving at Haight-Ashbury
solver.add(depart_russian <= patricia_end - (meeting_duration / 60))  # Must leave in time to meet for 30 minutes
solver.add(arrive_russian >= patricia_start)  # Must arrive at or after Patricia starts being available
solver.add(depart_patricia >= arrive_russian + (meeting_duration / 60))  # Must leave after meeting for 30 minutes

# Attempt to maximize meeting time with Patricia (ideally want to meet her for 30 minutes)
meet_time = min(depart_patricia - arrive_russian, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_russian_val = model[depart_russian].as_decimal(2)
    arrive_russian_val = model[arrive_russian].as_decimal(2)
    depart_patricia_val = model[depart_patricia].as_decimal(2)

    print(f"Depart from Haight-Ashbury to Russian Hill at: {depart_russian_val} hours")
    print(f"Arrive at Russian Hill at: {arrive_russian_val} hours")
    print(f"Depart from Russian Hill after meeting Patricia at: {depart_patricia_val} hours")
else:
    print("No valid schedule found.")