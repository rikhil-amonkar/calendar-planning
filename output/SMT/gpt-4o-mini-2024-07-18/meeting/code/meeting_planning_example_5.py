from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_castro = Real('depart_castro')  # Time at which we leave Nob Hill to head to The Castro
arrive_castro = Real('arrive_castro')  # Time at which we arrive at The Castro
depart_william = Real('depart_william')  # Time we leave The Castro after meeting with William

# Constants
travel_time_nobhill_to_castro = 17  # minutes
travel_time_castro_to_nobhill = 16   # minutes
meeting_duration = 75  # minutes
william_start = 12.25  # 12:15 PM in hours
william_end = 22.0    # 10:00 PM in hours
arrival_time_nobhill = 9.0  # 9:00 AM in hours

# Constraints
solver.add(arrive_castro == depart_castro + travel_time_nobhill_to_castro)
solver.add(depart_castro >= arrival_time_nobhill)  # Must leave after arriving at Nob Hill
solver.add(depart_castro <= william_end - meeting_duration)  # Must leave in time to meet for 75 minutes
solver.add(arrive_castro >= william_start)  # Must arrive at or after William starts being available
solver.add(depart_william >= arrive_castro + meeting_duration)  # Must leave after meeting for 75 minutes

# Maximize the meeting time with William (ideally want to meet him for 75 minutes)
meet_time = min(depart_william - arrive_castro, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_castro_val = model[depart_castro].as_decimal(2)
    arrive_castro_val = model[arrive_castro].as_decimal(2)
    depart_william_val = model[depart_william].as_decimal(2)
    
    print(f"Depart from Nob Hill to The Castro at: {depart_castro_val} hours")
    print(f"Arrive at The Castro at: {arrive_castro_val} hours")
    print(f"Depart from The Castro after meeting William at: {depart_william_val} hours")
else:
    print("No valid schedule found.")