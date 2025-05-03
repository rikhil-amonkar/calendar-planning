from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_russian_hill = Real('depart_russian_hill')  # Time we leave Bayview to head to Russian Hill
arrive_russian_hill = Real('arrive_russian_hill')  # Time we arrive at Russian Hill
depart_john = Real('depart_john')  # Time we leave Russian Hill after meeting with John

# Constants
travel_time_bayview_to_russian_hill = 23  # minutes
meeting_duration = 75                      # minutes
john_start = 17.5                          # 5:30 PM in hours
john_end = 21.0                            # 9:00 PM in hours
arrival_time_bayview = 9.0                 # 9:00 AM in hours

# Constraints
solver.add(arrive_russian_hill == depart_russian_hill + travel_time_bayview_to_russian_hill)
solver.add(depart_russian_hill >= arrival_time_bayview)  # Must leave after arriving at Bayview
solver.add(depart_russian_hill <= john_end - meeting_duration)  # Must leave in time to meet for 75 minutes
solver.add(arrive_russian_hill >= john_start)  # Must arrive at or after John starts being available
solver.add(depart_john >= arrive_russian_hill + meeting_duration)  # Must leave after meeting for 75 minutes

# Maximize the meeting time with John
meet_time = min(depart_john - arrive_russian_hill, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_russian_hill_val = model[depart_russian_hill].as_decimal(2)
    arrive_russian_hill_val = model[arrive_russian_hill].as_decimal(2)
    depart_john_val = model[depart_john].as_decimal(2)

    print(f"Depart from Bayview to Russian Hill at: {depart_russian_hill_val} hours")
    print(f"Arrive at Russian Hill at: {arrive_russian_hill_val} hours")
    print(f"Depart from Russian Hill after meeting John at: {depart_john_val} hours")
else:
    print("No valid schedule found.")