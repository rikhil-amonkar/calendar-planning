from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_financial = Real('depart_financial')  # Time you leave Bayview to head to Financial District
arrive_financial = Real('arrive_financial')  # Time you arrive at Financial District
depart_jeffrey = Real('depart_jeffrey')      # Time you leave Financial District after meeting with Jeffrey

# Constants
travel_time_bayview_to_financial = 19  # minutes
travel_time_financial_to_bayview = 19   # minutes
meeting_duration = 90                   # minutes
jeffrey_start = 12.25                   # 12:15 PM in hours
jeffrey_end = 14.0                      # 2:00 PM in hours
arrival_time_bayview = 9.0              # 9:00 AM in hours

# Constraints
solver.add(arrive_financial == depart_financial + travel_time_bayview_to_financial)
solver.add(depart_financial >= arrival_time_bayview)  # Must leave after arriving at Bayview
solver.add(depart_financial <= jeffrey_end - meeting_duration)  # Must leave in time to meet for 90 minutes
solver.add(arrive_financial >= jeffrey_start)  # Must arrive at or after Jeffrey starts being available
solver.add(depart_jeffrey >= arrive_financial + meeting_duration)  # Must leave after meeting for 90 minutes

# Maximize the meeting time with Jeffrey (ideally want to meet him for 90 minutes)
meet_time = min(depart_jeffrey - arrive_financial, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_financial_val = model[depart_financial].as_decimal(2)
    arrive_financial_val = model[arrive_financial].as_decimal(2)
    depart_jeffrey_val = model[depart_jeffrey].as_decimal(2)

    print(f"Depart from Bayview to Financial District at: {depart_financial_val} hours")
    print(f"Arrive at Financial District at: {arrive_financial_val} hours")
    print(f"Depart from Financial District after meeting Jeffrey at: {depart_jeffrey_val} hours")
else:
    print("No valid schedule found.")