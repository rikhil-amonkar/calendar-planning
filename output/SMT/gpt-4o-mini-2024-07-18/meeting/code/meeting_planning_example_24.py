from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_presidio = Real('depart_presidio')  # Time we leave Nob Hill to head to Presidio
arrive_presidio = Real('arrive_presidio')  # Time we arrive at Presidio
depart_matthew = Real('depart_matthew')  # Time we leave Presidio after meeting with Matthew

# Constants
travel_time_nob_hill_to_presidio = 17  # minutes
meeting_duration = 30                    # minutes
matthew_start = 11.0                    # 11:00 AM in hours
matthew_end = 15.25                      # 3:15 PM in hours
arrival_time_nob_hill = 9.0             # 9:00 AM in hours

# Constraints
solver.add(arrive_presidio == depart_presidio + travel_time_nob_hill_to_presidio)
solver.add(depart_presidio >= arrival_time_nob_hill)  # Must leave after arriving at Nob Hill
solver.add(depart_presidio <= matthew_end - meeting_duration)  # Must leave in time to meet for 30 minutes
solver.add(arrive_presidio >= matthew_start)  # Must arrive at or after Matthew starts being available
solver.add(depart_matthew >= arrive_presidio + meeting_duration)  # Must leave after meeting for 30 minutes

# Maximize the meeting time with Matthew (ideally want to meet him for 30 minutes)
meet_time = min(depart_matthew - arrive_presidio, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_presidio_val = model[depart_presidio].as_decimal(2)
    arrive_presidio_val = model[arrive_presidio].as_decimal(2)
    depart_matthew_val = model[depart_matthew].as_decimal(2)

    print(f"Depart from Nob Hill to Presidio at: {depart_presidio_val} hours")
    print(f"Arrive at Presidio at: {arrive_presidio_val} hours")
    print(f"Depart from Presidio after meeting Matthew at: {depart_matthew_val} hours")
else:
    print("No valid schedule found.")