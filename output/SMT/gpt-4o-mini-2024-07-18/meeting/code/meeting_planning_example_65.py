from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_embarcadero = Real('depart_embarcadero')  # Time you leave Golden Gate Park to head to Embarcadero
arrive_embarcadero = Real('arrive_embarcadero')  # Time you arrive at Embarcadero
depart_sandra = Real('depart_sandra')              # Time you leave Embarcadero after meeting Sandra

# Constants
travel_time_ggp_to_embarcadero = 25  # minutes from Golden Gate Park to Embarcadero
travel_time_embarcadero_to_ggp = 25   # minutes from Embarcadero back to Golden Gate Park
meeting_duration = 45                  # minimum meeting duration (in minutes)
sandra_start = 19.0                   # 7:00 PM in hours
sandra_end = 21.0                     # 9:00 PM in hours
arrival_time_ggp = 9.0                # 9:00 AM in hours

# Constraints
solver.add(arrive_embarcadero == depart_embarcadero + travel_time_ggp_to_embarcadero)  # Arrival time at Embarcadero
solver.add(depart_embarcadero >= arrival_time_ggp)  # Must leave after arriving at Golden Gate Park
solver.add(depart_embarcadero <= sandra_end - (meeting_duration / 60))  # Must leave in time to meet for 45 minutes
solver.add(arrive_embarcadero >= sandra_start)  # Must arrive at or after Sandra starts being available
solver.add(depart_sandra >= arrive_embarcadero + (meeting_duration / 60))  # Must leave after meeting for 45 minutes

# Maximize the meeting time with Sandra (ideally want to meet her for 45 minutes)
meet_time = min(depart_sandra - arrive_embarcadero, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_embarcadero_val = model[depart_embarcadero].as_decimal(2)
    arrive_embarcadero_val = model[arrive_embarcadero].as_decimal(2)
    depart_sandra_val = model[depart_sandra].as_decimal(2)

    print(f"Depart from Golden Gate Park to Embarcadero at: {depart_embarcadero_val} hours")
    print(f"Arrive at Embarcadero at: {arrive_embarcadero_val} hours")
    print(f"Depart from Embarcadero after meeting Sandra at: {depart_sandra_val} hours")
else:
    print("No valid schedule found.")