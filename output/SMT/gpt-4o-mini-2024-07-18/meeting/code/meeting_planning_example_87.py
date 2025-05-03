from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_pacific = Real('depart_pacific')  # Time you leave Embarcadero to head to Pacific Heights
arrive_pacific = Real('arrive_pacific')  # Time you arrive at Pacific Heights
depart_james = Real('depart_james')       # Time you leave Pacific Heights after meeting James

# Constants
travel_time_embarcadero_to_pacific = 11  # minutes from Embarcadero to Pacific Heights
travel_time_pacific_to_embarcadero = 10   # minutes from Pacific Heights back to Embarcadero
meeting_duration = 75                      # minimum meeting duration (in minutes)
james_start = 8.5                         # 8:30 AM in hours
james_end = 15.0                          # 3:00 PM in hours
arrival_time_embarcadero = 9.0            # 9:00 AM in hours

# Constraints
solver.add(arrive_pacific == depart_pacific + travel_time_embarcadero_to_pacific)  # Arrival time at Pacific Heights
solver.add(depart_pacific >= arrival_time_embarcadero)  # Must leave after arriving at Embarcadero
solver.add(depart_pacific <= james_end - (meeting_duration / 60))  # Must leave in time to meet for 75 minutes
solver.add(arrive_pacific >= james_start)  # Must arrive at or after James starts being available
solver.add(depart_james >= arrive_pacific + (meeting_duration / 60))  # Must leave after meeting for 75 minutes

# Maximize the meeting time with James (ideally we want to meet him for at least 75 minutes)
meet_time = min(depart_james - arrive_pacific, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_pacific_val = model[depart_pacific].as_decimal(2)
    arrive_pacific_val = model[arrive_pacific].as_decimal(2)
    depart_james_val = model[depart_james].as_decimal(2)

    print(f"Depart from Embarcadero to Pacific Heights at: {depart_pacific_val} hours")
    print(f"Arrive at Pacific Heights at: {arrive_pacific_val} hours")
    print(f"Depart from Pacific Heights after meeting James at: {depart_james_val} hours")
else:
    print("No valid schedule found.")