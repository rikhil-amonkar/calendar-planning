from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_pacific = Real('depart_pacific')  # Time we leave Bayview to head to Pacific Heights
arrive_pacific = Real('arrive_pacific')  # Time we arrive at Pacific Heights
depart_thomas = Real('depart_thomas')     # Time we leave Pacific Heights after meeting with Thomas

# Constants
travel_time_bayview_to_pacific = 23  # minutes
travel_time_pacific_to_bayview = 22   # minutes
meeting_duration = 105                # minutes
thomas_start = 12.25                  # 12:15 PM in hours
thomas_end = 17.25                    # 5:15 PM in hours
arrival_time_bayview = 9.0            # 9:00 AM in hours

# Constraints
solver.add(arrive_pacific == depart_pacific + travel_time_bayview_to_pacific)
solver.add(depart_pacific >= arrival_time_bayview)  # Must leave after arriving at Bayview
solver.add(depart_pacific <= thomas_end - meeting_duration)  # Must leave in time to meet for 105 minutes
solver.add(arrive_pacific >= thomas_start)  # Must arrive at or after Thomas starts being available
solver.add(depart_thomas >= arrive_pacific + meeting_duration)  # Must leave after meeting for 105 minutes

# Maximize the meeting time with Thomas (ideally want to meet him for 105 minutes)
meet_time = min(depart_thomas - arrive_pacific, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_pacific_val = model[depart_pacific].as_decimal(2)
    arrive_pacific_val = model[arrive_pacific].as_decimal(2)
    depart_thomas_val = model[depart_thomas].as_decimal(2)

    print(f"Depart from Bayview to Pacific Heights at: {depart_pacific_val} hours")
    print(f"Arrive at Pacific Heights at: {arrive_pacific_val} hours")
    print(f"Depart from Pacific Heights after meeting Thomas at: {depart_thomas_val} hours")
else:
    print("No valid schedule found.")