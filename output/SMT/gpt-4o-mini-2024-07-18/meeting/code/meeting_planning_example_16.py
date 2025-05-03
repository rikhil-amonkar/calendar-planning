from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_russian_hill = Real('depart_russian_hill')  # Time at which we leave Chinatown to head to Russian Hill
arrive_russian_hill = Real('arrive_russian_hill')  # Time at which we arrive at Russian Hill
depart_ronald = Real('depart_ronald')  # Time we leave Russian Hill after meeting Ronald

# Constants
travel_time_chinatown_to_russian_hill = 7   # minutes
travel_time_russian_hill_to_chinatown = 9    # minutes
meeting_duration = 105                         # minutes
ronald_start = 15.25                          # 3:15 PM in hours
ronald_end = 21.5                             # 9:30 PM in hours
arrival_time_chinatown = 9.0                  # 9:00 AM in hours

# Constraints
solver.add(arrive_russian_hill == depart_russian_hill + travel_time_chinatown_to_russian_hill)
solver.add(depart_russian_hill >= arrival_time_chinatown)  # Must leave after arriving at Chinatown
solver.add(depart_russian_hill <= ronald_end - meeting_duration)  # Must leave in time to meet for 105 minutes
solver.add(arrive_russian_hill >= ronald_start)  # Must arrive at or after Ronald starts being available
solver.add(depart_ronald >= arrive_russian_hill + meeting_duration)  # Must leave after meeting for 105 minutes

# Maximize the meeting time with Ronald (ideally want to meet him for 105 minutes)
meet_time = min(depart_ronald - arrive_russian_hill, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_russian_hill_val = model[depart_russian_hill].as_decimal(2)
    arrive_russian_hill_val = model[arrive_russian_hill].as_decimal(2)
    depart_ronald_val = model[depart_ronald].as_decimal(2)

    print(f"Depart from Chinatown to Russian Hill at: {depart_russian_hill_val} hours")
    print(f"Arrive at Russian Hill at: {arrive_russian_hill_val} hours")
    print(f"Depart from Russian Hill after meeting Ronald at: {depart_ronald_val} hours")
else:
    print("No valid schedule found.")