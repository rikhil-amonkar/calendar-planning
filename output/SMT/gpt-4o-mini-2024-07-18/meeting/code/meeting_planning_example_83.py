from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_ggp = Real('depart_ggp')      # Time you leave Presidio to head to Golden Gate Park
arrive_ggp = Real('arrive_ggp')      # Time you arrive at Golden Gate Park
depart_carol = Real('depart_carol')   # Time you leave Golden Gate Park after meeting Carol

# Constants
travel_time_presidio_to_ggp = 12     # minutes from Presidio to Golden Gate Park
travel_time_ggp_to_presidio = 11      # minutes from Golden Gate Park to Presidio
meeting_duration = 45                  # minimum meeting duration (in minutes)
carol_start = 21.75                   # 9:45 PM in hours
carol_end = 22.5                      # 10:30 PM in hours
arrival_time_presidio = 9.0            # 9:00 AM in hours

# Constraints
solver.add(arrive_ggp == depart_ggp + travel_time_presidio_to_ggp)  # Arrival time at Golden Gate Park
solver.add(depart_ggp >= arrival_time_presidio)  # Must leave after arriving at Presidio
solver.add(depart_ggp <= carol_end - (meeting_duration / 60))  # Must leave in time to meet for 45 minutes
solver.add(arrive_ggp >= carol_start)  # Must arrive at or after Carol starts being available
solver.add(depart_carol >= arrive_ggp + (meeting_duration / 60))  # Must leave after meeting for 45 minutes

# Maximize the meeting time with Carol (ideally want to meet her for at least 45 minutes)
meet_time = min(depart_carol - arrive_ggp, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_ggp_val = model[depart_ggp].as_decimal(2)
    arrive_ggp_val = model[arrive_ggp].as_decimal(2)
    depart_carol_val = model[depart_carol].as_decimal(2)

    print(f"Depart from Presidio to Golden Gate Park at: {depart_ggp_val} hours")
    print(f"Arrive at Golden Gate Park at: {arrive_ggp_val} hours")
    print(f"Depart from Golden Gate Park after meeting Carol at: {depart_carol_val} hours")
else:
    print("No valid schedule found.")