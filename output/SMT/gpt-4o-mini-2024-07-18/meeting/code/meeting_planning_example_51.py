from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_embarcadero = Real('depart_embarcadero')  # Time you leave The Castro to head to Embarcadero
arrive_embarcadero = Real('arrive_embarcadero')  # Time you arrive at Embarcadero
depart_laura = Real('depart_laura')                # Time you leave Embarcadero after meeting Laura

# Constants
travel_time_castro_to_embarcadero = 22  # minutes from The Castro to Embarcadero
travel_time_embarcadero_to_castro = 25   # minutes from Embarcadero to The Castro
meeting_duration = 15                     # minimum meeting duration (in minutes)
laura_start = 8.0                        # 8:00 AM in hours
laura_end = 11.0                         # 11:00 AM in hours
arrival_time_castro = 9.0                 # 9:00 AM in hours

# Constraints
solver.add(arrive_embarcadero == depart_embarcadero + travel_time_castro_to_embarcadero)  # Arrival time at Embarcadero
solver.add(depart_embarcadero >= arrival_time_castro)  # Must leave after arriving at The Castro
solver.add(depart_embarcadero <= laura_end - (meeting_duration / 60))  # Must leave in time to meet for 15 minutes
solver.add(arrive_embarcadero >= laura_start)  # Must arrive at or after Laura starts being available
solver.add(depart_laura >= arrive_embarcadero + (meeting_duration / 60))  # Must leave after meeting for 15 minutes

# Maximize the meeting time with Laura (ideally want to meet her for 15 minutes)
meet_time = min(depart_laura - arrive_embarcadero, meeting_duration / 60)  # in hours

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_embarcadero_val = model[depart_embarcadero].as_decimal(2)
    arrive_embarcadero_val = model[arrive_embarcadero].as_decimal(2)
    depart_laura_val = model[depart_laura].as_decimal(2)

    print(f"Depart from The Castro to Embarcadero at: {depart_embarcadero_val} hours")
    print(f"Arrive at Embarcadero at: {arrive_embarcadero_val} hours")
    print(f"Depart from Embarcadero after meeting Laura at: {depart_laura_val} hours")
else:
    print("No valid schedule found.")