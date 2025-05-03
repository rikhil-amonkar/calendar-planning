from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_richmond = Real('depart_richmond')  # Time you leave Russian Hill to head to Richmond District
arrive_richmond = Real('arrive_richmond')  # Time you arrive at Richmond District
depart_daniel = Real('depart_daniel')       # Time you leave Richmond District after meeting Daniel

# Constants
travel_time_russian_to_richmond = 14       # minutes from Russian Hill to Richmond District
travel_time_richmond_to_russian = 13        # minutes from Richmond District back to Russian Hill
meeting_duration = 75                        # minimum meeting duration (in minutes)
daniel_start = 19.0                         # 7:00 PM in hours
daniel_end = 20.25                          # 8:15 PM in hours
arrival_time_russian = 9.0                  # 9:00 AM in hours

# Constraints
solver.add(arrive_richmond == depart_richmond + travel_time_russian_to_richmond)  # Arrival time at Richmond District
solver.add(depart_richmond >= arrival_time_russian)  # Must leave after arriving at Russian Hill
solver.add(depart_richmond <= daniel_end - (meeting_duration / 60))  # Must leave in time to meet for 75 minutes
solver.add(arrive_richmond >= daniel_start)  # Must arrive at or after Daniel starts being available
solver.add(depart_daniel >= arrive_richmond + (meeting_duration / 60))  # Must leave after meeting for 75 minutes

# Maximize the meeting time with Daniel (ideally we want to meet him for at least 75 minutes)
meet_time = min(depart_daniel - arrive_richmond, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_richmond_val = model[depart_richmond].as_decimal(2)
    arrive_richmond_val = model[arrive_richmond].as_decimal(2)
    depart_daniel_val = model[depart_daniel].as_decimal(2)

    print(f"Depart from Russian Hill to Richmond District at: {depart_richmond_val} hours")
    print(f"Arrive at Richmond District at: {arrive_richmond_val} hours")
    print(f"Depart from Richmond District after meeting Daniel at: {depart_daniel_val} hours")
else:
    print("No valid schedule found.")