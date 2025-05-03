from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_embarcadero = Real('depart_embarcadero')  # Time you leave Marina District to head to Embarcadero
arrive_embarcadero = Real('arrive_embarcadero')  # Time you arrive at Embarcadero
depart_barbara = Real('depart_barbara')            # Time you leave Embarcadero after meeting with Barbara

# Constants
travel_time_marina_to_embarcadero = 14  # minutes
travel_time_embarcadero_to_marina = 12   # minutes
meeting_duration = 60                    # minutes
barbara_start = 13.5                     # 1:30 PM in hours
barbara_end = 20.75                      # 8:45 PM in hours
arrival_time_marina = 9.0                # 9:00 AM in hours

# Constraints
solver.add(arrive_embarcadero == depart_embarcadero + travel_time_marina_to_embarcadero)
solver.add(depart_embarcadero >= arrival_time_marina)  # Must leave after arriving at Marina District
solver.add(depart_embarcadero <= barbara_end - meeting_duration)  # Must leave in time to meet for 60 minutes
solver.add(arrive_embarcadero >= barbara_start)  # Must arrive at or after Barbara starts being available
solver.add(depart_barbara >= arrive_embarcadero + meeting_duration)  # Must leave after meeting for 60 minutes

# Maximize the meeting time with Barbara (ideally want to meet for 60 minutes)
meet_time = min(depart_barbara - arrive_embarcadero, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_embarcadero_val = model[depart_embarcadero].as_decimal(2)
    arrive_embarcadero_val = model[arrive_embarcadero].as_decimal(2)
    depart_barbara_val = model[depart_barbara].as_decimal(2)

    print(f"Depart from Marina District to Embarcadero at: {depart_embarcadero_val} hours")
    print(f"Arrive at Embarcadero at: {arrive_embarcadero_val} hours")
    print(f"Depart from Embarcadero after meeting Barbara at: {depart_barbara_val} hours")
else:
    print("No valid schedule found.")