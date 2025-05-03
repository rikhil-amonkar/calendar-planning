from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_richmond = Real('depart_richmond')  # Time you leave Russian Hill to head to Richmond District
arrive_richmond = Real('arrive_richmond')  # Time you arrive at Richmond District
depart_barbara = Real('depart_barbara')     # Time you leave Richmond District after meeting Barbara

# Constants
travel_time_russian_to_richmond = 14  # minutes from Russian Hill to Richmond District
travel_time_richmond_to_russian = 13   # minutes from Richmond District to Russian Hill
meeting_duration = 45                   # minimum meeting duration (in minutes)
barbara_start = 13.25                  # 1:15 PM in hours
barbara_end = 18.25                    # 6:15 PM in hours
arrival_time_russian = 9.0             # 9:00 AM in hours

# Constraints
solver.add(arrive_richmond == depart_richmond + travel_time_russian_to_richmond)  # Arrival time at Richmond District
solver.add(depart_richmond >= arrival_time_russian)  # Must leave after arriving at Russian Hill
solver.add(depart_richmond <= barbara_end - (meeting_duration / 60))  # Must leave in time to meet for 45 minutes
solver.add(arrive_richmond >= barbara_start)  # Must arrive at or after Barbara starts being available
solver.add(depart_barbara >= arrive_richmond + (meeting_duration / 60))  # Must leave after meeting for 45 minutes

# Maximize the meeting time with Barbara (ideally want to meet her for 45 minutes)
meet_time = min(depart_barbara - arrive_richmond, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_richmond_val = model[depart_richmond].as_decimal(2)
    arrive_richmond_val = model[arrive_richmond].as_decimal(2)
    depart_barbara_val = model[depart_barbara].as_decimal(2)

    print(f"Depart from Russian Hill to Richmond District at: {depart_richmond_val} hours")
    print(f"Arrive at Richmond District at: {arrive_richmond_val} hours")
    print(f"Depart from Richmond District after meeting Barbara at: {depart_barbara_val} hours")
else:
    print("No valid schedule found.")