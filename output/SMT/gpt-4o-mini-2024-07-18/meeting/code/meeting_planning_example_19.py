from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_pacific = Real('depart_pacific')  # Time at which we leave Golden Gate Park to head to Pacific Heights
arrive_pacific = Real('arrive_pacific')  # Time at which we arrive at Pacific Heights
depart_john = Real('depart_john')  # Time we leave Pacific Heights after meeting with John

# Constants
travel_time_golden_gate_to_pacific = 16  # minutes
meeting_duration = 45                      # minutes
john_start = 19.75                        # 7:45 PM in hours
john_end = 20.75                          # 8:45 PM in hours
arrival_time_golden_gate = 9.0           # 9:00 AM in hours

# Constraints
solver.add(arrive_pacific == depart_pacific + travel_time_golden_gate_to_pacific)
solver.add(depart_pacific >= arrival_time_golden_gate)  # Must leave after arriving at Golden Gate Park
solver.add(depart_pacific <= john_end - meeting_duration)  # Must leave in time to meet for 45 minutes
solver.add(arrive_pacific >= john_start)  # Must arrive at or after John starts being available
solver.add(depart_john >= arrive_pacific + meeting_duration)  # Must leave after meeting for 45 minutes

# Maximize the meeting time with John (ideally want to meet him for 45 minutes)
meet_time = min(depart_john - arrive_pacific, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_pacific_val = model[depart_pacific].as_decimal(2)
    arrive_pacific_val = model[arrive_pacific].as_decimal(2)
    depart_john_val = model[depart_john].as_decimal(2)

    print(f"Depart from Golden Gate Park to Pacific Heights at: {depart_pacific_val} hours")
    print(f"Arrive at Pacific Heights at: {arrive_pacific_val} hours")
    print(f"Depart from Pacific Heights after meeting John at: {depart_john_val} hours")
else:
    print("No valid schedule found.")