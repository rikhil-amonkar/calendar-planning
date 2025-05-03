from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_presidio = Real('depart_presidio')  # Time we leave Richmond District to head to Presidio
arrive_presidio = Real('arrive_presidio')  # Time we arrive at Presidio
depart_sarah = Real('depart_sarah')  # Time we leave Presidio after meeting with Sarah

# Constants
travel_time_richmond_to_presidio = 7  # minutes
meeting_duration = 105                  # minutes
sarah_start = 13.25                    # 1:15 PM in hours
sarah_end = 15.25                      # 3:15 PM in hours
arrival_time_richmond = 9.0            # 9:00 AM in hours

# Constraints
solver.add(arrive_presidio == depart_presidio + travel_time_richmond_to_presidio)
solver.add(depart_presidio >= arrival_time_richmond)  # Must leave after arriving at Richmond District
solver.add(depart_presidio <= sarah_end - meeting_duration)  # Must leave in time to meet for 105 minutes
solver.add(arrive_presidio >= sarah_start)  # Must arrive at or after Sarah starts being available
solver.add(depart_sarah >= arrive_presidio + meeting_duration)  # Must leave after meeting for 105 minutes

# Maximize the meeting time with Sarah (ideally want to meet for 105 minutes)
meet_time = min(depart_sarah - arrive_presidio, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_presidio_val = model[depart_presidio].as_decimal(2)
    arrive_presidio_val = model[arrive_presidio].as_decimal(2)
    depart_sarah_val = model[depart_sarah].as_decimal(2)

    print(f"Depart from Richmond District to Presidio at: {depart_presidio_val} hours")
    print(f"Arrive at Presidio at: {arrive_presidio_val} hours")
    print(f"Depart from Presidio after meeting Sarah at: {depart_sarah_val} hours")
else:
    print("No valid schedule found.")