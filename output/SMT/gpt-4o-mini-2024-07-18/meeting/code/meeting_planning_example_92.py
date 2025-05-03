from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_castro = Real('depart_castro')  # Time you leave Financial District to head to The Castro
arrive_castro = Real('arrive_castro')  # Time you arrive at The Castro
depart_carol = Real('depart_carol')     # Time you leave The Castro after meeting Carol

# Constants
travel_time_financial_to_castro = 23   # minutes from Financial District to The Castro
travel_time_castro_to_financial = 20    # minutes from The Castro to Financial District
meeting_duration = 45                    # minimum meeting duration (in minutes)
carol_start = 14.0                      # 2:00 PM in hours
carol_end = 17.75                        # 5:45 PM in hours
arrival_time_financial = 9.0             # 9:00 AM in hours

# Constraints
solver.add(arrive_castro == depart_castro + travel_time_financial_to_castro)  # Arrival time at The Castro
solver.add(depart_castro >= arrival_time_financial)  # Must leave after arriving at Financial District
solver.add(depart_castro <= carol_end - (meeting_duration / 60))  # Must leave in time to meet for 45 minutes
solver.add(arrive_castro >= carol_start)  # Must arrive at or after Carol starts being available
solver.add(depart_carol >= arrive_castro + (meeting_duration / 60))  # Must leave after meeting for 45 minutes

# Maximize the meeting time with Carol (ideally want to meet her for at least 45 minutes)
meet_time = min(depart_carol - arrive_castro, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_castro_val = model[depart_castro].as_decimal(2)
    arrive_castro_val = model[arrive_castro].as_decimal(2)
    depart_carol_val = model[depart_carol].as_decimal(2)

    print(f"Depart from Financial District to The Castro at: {depart_castro_val} hours")
    print(f"Arrive at The Castro at: {arrive_castro_val} hours")
    print(f"Depart from The Castro after meeting Carol at: {depart_carol_val} hours")
else:
    print("No valid schedule found.")