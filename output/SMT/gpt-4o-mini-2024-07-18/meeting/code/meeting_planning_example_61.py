from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_presidio = Real('depart_presidio')  # Time you leave Golden Gate Park to head to Presidio
arrive_presidio = Real('arrive_presidio')  # Time you arrive at Presidio
depart_stephanie = Real('depart_stephanie')  # Time you leave Presidio after meeting Stephanie

# Constants
travel_time_ggp_to_presidio = 11  # minutes from Golden Gate Park to Presidio
travel_time_presidio_to_ggp = 12   # minutes from Presidio back to Golden Gate Park
meeting_duration = 90               # minimum meeting duration (in minutes)
stephanie_start = 19.25             # 7:15 PM in hours
stephanie_end = 22.0                # 10:00 PM in hours
arrival_time_ggp = 9.0              # 9:00 AM in hours

# Constraints
solver.add(arrive_presidio == depart_presidio + travel_time_ggp_to_presidio)  # Arrival time at Presidio
solver.add(depart_presidio >= arrival_time_ggp)  # Must leave after arriving at Golden Gate Park
solver.add(depart_presidio <= stephanie_end - (meeting_duration / 60))  # Must leave in time to meet for 90 minutes
solver.add(arrive_presidio >= stephanie_start)  # Must arrive at or after Stephanie starts being available
solver.add(depart_stephanie >= arrive_presidio + (meeting_duration / 60))  # Must leave after meeting for 90 minutes

# Maximize the meeting time with Stephanie (ideally want to meet her for 90 minutes)
meet_time = min(depart_stephanie - arrive_presidio, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_presidio_val = model[depart_presidio].as_decimal(2)
    arrive_presidio_val = model[arrive_presidio].as_decimal(2)
    depart_stephanie_val = model[depart_stephanie].as_decimal(2)

    print(f"Depart from Golden Gate Park to Presidio at: {depart_presidio_val} hours")
    print(f"Arrive at Presidio at: {arrive_presidio_val} hours")
    print(f"Depart from Presidio after meeting Stephanie at: {depart_stephanie_val} hours")
else:
    print("No valid schedule found.")