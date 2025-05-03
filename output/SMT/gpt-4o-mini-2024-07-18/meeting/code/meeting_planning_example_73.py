from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_pacific = Real('depart_pacific')  # Time you leave Russian Hill to head to Pacific Heights
arrive_pacific = Real('arrive_pacific')  # Time you arrive at Pacific Heights
depart_barbara = Real('depart_barbara')   # Time you leave Pacific Heights after meeting Barbara

# Constants
travel_time_russian_to_pacific = 7  # minutes from Russian Hill to Pacific Heights
travel_time_pacific_to_russian = 7   # minutes from Pacific Heights to Russian Hill
meeting_duration = 60                 # minimum meeting duration (in minutes)
barbara_start = 7 + 15 / 60          # 7:15 AM in hours
barbara_end = 22.0                   # 10:00 PM in hours
arrival_time_russian = 9.0            # 9:00 AM in hours

# Constraints
solver.add(arrive_pacific == depart_pacific + travel_time_russian_to_pacific)  # Arrival time at Pacific Heights
solver.add(depart_pacific >= arrival_time_russian)  # Must leave after arriving at Russian Hill
solver.add(depart_pacific <= barbara_end - (meeting_duration / 60))  # Must leave in time to meet for 60 minutes
solver.add(arrive_pacific >= barbara_start)  # Must arrive at or after Barbara starts being available
solver.add(depart_barbara >= arrive_pacific + (meeting_duration / 60))  # Must leave after meeting for 60 minutes

# Maximize the meeting time with Barbara (ideally want to meet her for 60 minutes)
meet_time = min(depart_barbara - arrive_pacific, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_pacific_val = model[depart_pacific].as_decimal(2)
    arrive_pacific_val = model[arrive_pacific].as_decimal(2)
    depart_barbara_val = model[depart_barbara].as_decimal(2)

    print(f"Depart from Russian Hill to Pacific Heights at: {depart_pacific_val} hours")
    print(f"Arrive at Pacific Heights at: {arrive_pacific_val} hours")
    print(f"Depart from Pacific Heights after meeting Barbara at: {depart_barbara_val} hours")
else:
    print("No valid schedule found.")