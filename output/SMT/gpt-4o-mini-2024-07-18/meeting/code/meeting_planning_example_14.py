from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_marina = Real('depart_marina')  # Time at which we leave Nob Hill to head to Marina District
arrive_marina = Real('arrive_marina')  # Time at which we arrive at Marina District
depart_mary = Real('depart_mary')  # Time we leave Marina District after meeting with Mary

# Constants
travel_time_nobhill_to_marina = 11  # minutes
meeting_duration = 120  # minutes
mary_start = 20.0       # 8:00 PM in hours
mary_end = 22.0         # 10:00 PM in hours
arrival_time_nobhill = 9.0  # 9:00 AM in hours

# Constraints
solver.add(arrive_marina == depart_marina + travel_time_nobhill_to_marina)
solver.add(depart_marina >= arrival_time_nobhill)  # Must leave after arriving at Nob Hill
solver.add(depart_marina <= mary_end - meeting_duration)  # Must leave in time to meet for 120 minutes
solver.add(arrive_marina >= mary_start)  # Must arrive at or after Mary starts being available
solver.add(depart_mary >= arrive_marina + meeting_duration)  # Must leave after meeting for 120 minutes

# Maximize the meeting time with Mary (ideally want to meet her for 120 minutes)
meet_time = min(depart_mary - arrive_marina, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_marina_val = model[depart_marina].as_decimal(2)
    arrive_marina_val = model[arrive_marina].as_decimal(2)
    depart_mary_val = model[depart_mary].as_decimal(2)

    print(f"Depart from Nob Hill to Marina District at: {depart_marina_val} hours")
    print(f"Arrive at Marina District at: {arrive_marina_val} hours")
    print(f"Depart from Marina District after meeting Mary at: {depart_mary_val} hours")
else:
    print("No valid schedule found.")