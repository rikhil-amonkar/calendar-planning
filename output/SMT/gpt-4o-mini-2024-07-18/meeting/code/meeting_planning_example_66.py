from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_presidio = Real('depart_presidio')  # Time you leave Nob Hill to head to Presidio
arrive_presidio = Real('arrive_presidio')  # Time you arrive at Presidio
depart_robert = Real('depart_robert')       # Time you leave Presidio after meeting Robert

# Constants
travel_time_nob_to_presidio = 17  # minutes from Nob Hill to Presidio
travel_time_presidio_to_nob = 18   # minutes from Presidio back to Nob Hill
meeting_duration = 120              # minimum meeting duration (in minutes)
robert_start = 11.25               # 11:15 AM in hours
robert_end = 17.75                 # 5:45 PM in hours
arrival_time_nob = 9.0             # 9:00 AM in hours

# Constraints
solver.add(arrive_presidio == depart_presidio + travel_time_nob_to_presidio)  # Arrival time at Presidio
solver.add(depart_presidio >= arrival_time_nob)  # Must leave after arriving at Nob Hill
solver.add(depart_presidio <= robert_end - (meeting_duration / 60))  # Must leave in time to meet for 120 minutes
solver.add(arrive_presidio >= robert_start)  # Must arrive at or after Robert starts being available
solver.add(depart_robert >= arrive_presidio + (meeting_duration / 60))  # Must leave after meeting for 120 minutes

# Maximize the meeting time with Robert (ideally want to meet him for 120 minutes)
meet_time = min(depart_robert - arrive_presidio, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_presidio_val = model[depart_presidio].as_decimal(2)
    arrive_presidio_val = model[arrive_presidio].as_decimal(2)
    depart_robert_val = model[depart_robert].as_decimal(2)

    print(f"Depart from Nob Hill to Presidio at: {depart_presidio_val} hours")
    print(f"Arrive at Presidio at: {arrive_presidio_val} hours")
    print(f"Depart from Presidio after meeting Robert at: {depart_robert_val} hours")
else:
    print("No valid schedule found.")