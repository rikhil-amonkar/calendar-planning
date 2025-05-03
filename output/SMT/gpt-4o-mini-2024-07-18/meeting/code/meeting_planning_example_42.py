from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_presidio = Real('depart_presidio')  # Time you leave Nob Hill to head to Presidio
arrive_presidio = Real('arrive_presidio')  # Time you arrive at Presidio
depart_timothy = Real('depart_timothy')     # Time you leave Presidio after meeting Timothy

# Constants
travel_time_nob_hill_to_presidio = 17  # minutes
travel_time_presidio_to_nob_hill = 18   # minutes
meeting_duration = 30                   # minutes
timothy_start = 13.0                    # 1:00 PM in hours
timothy_end = 19.0                      # 7:00 PM in hours
arrival_time_nob_hill = 9.0             # 9:00 AM in hours

# Constraints
solver.add(arrive_presidio == depart_presidio + travel_time_nob_hill_to_presidio)  # Arrival time at Presidio
solver.add(depart_presidio >= arrival_time_nob_hill)  # Must leave after arriving at Nob Hill
solver.add(depart_presidio <= timothy_end - meeting_duration)  # Must leave in time to meet for 30 minutes
solver.add(arrive_presidio >= timothy_start)  # Must arrive at or after Timothy starts being available
solver.add(depart_timothy >= arrive_presidio + meeting_duration)  # Must leave after meeting for 30 minutes

# Maximize the meeting time with Timothy (ideally want to meet him for 30 minutes)
meet_time = min(depart_timothy - arrive_presidio, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_presidio_val = model[depart_presidio].as_decimal(2)
    arrive_presidio_val = model[arrive_presidio].as_decimal(2)
    depart_timothy_val = model[depart_timothy].as_decimal(2)

    print(f"Depart from Nob Hill to Presidio at: {depart_presidio_val} hours")
    print(f"Arrive at Presidio at: {arrive_presidio_val} hours")
    print(f"Depart from Presidio after meeting Timothy at: {depart_timothy_val} hours")
else:
    print("No valid schedule found.")