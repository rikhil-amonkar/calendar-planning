from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_russian = Real('depart_russian')  # Time you leave Presidio to head to Russian Hill
arrive_russian = Real('arrive_russian')  # Time you arrive at Russian Hill
depart_amanda = Real('depart_amanda')     # Time you leave Russian Hill after meeting Amanda

# Constants
travel_time_presidio_to_russian = 14  # minutes from Presidio to Russian Hill
travel_time_russian_to_presidio = 14   # minutes from Russian Hill to Presidio
meeting_duration = 15                   # minimum meeting duration (in minutes)
amanda_start = 11.5                    # 11:30 AM in hours
amanda_end = 21.25                      # 9:15 PM in hours
arrival_time_presidio = 9.0             # 9:00 AM in hours

# Constraints
solver.add(arrive_russian == depart_russian + travel_time_presidio_to_russian)  # Arrival time at Russian Hill
solver.add(depart_russian >= arrival_time_presidio)  # Must leave after arriving at Presidio
solver.add(depart_russian <= amanda_end - (meeting_duration / 60))  # Must leave in time to meet for 15 minutes
solver.add(arrive_russian >= amanda_start)  # Must arrive at or after Amanda starts being available
solver.add(depart_amanda >= arrive_russian + (meeting_duration / 60))  # Must leave after meeting for 15 minutes

# Maximize the meeting time with Amanda (ideally want to meet her for 15 minutes)
meet_time = min(depart_amanda - arrive_russian, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_russian_val = model[depart_russian].as_decimal(2)
    arrive_russian_val = model[arrive_russian].as_decimal(2)
    depart_amanda_val = model[depart_amanda].as_decimal(2)

    print(f"Depart from Presidio to Russian Hill at: {depart_russian_val} hours")
    print(f"Arrive at Russian Hill at: {arrive_russian_val} hours")
    print(f"Depart from Russian Hill after meeting Amanda at: {depart_amanda_val} hours")
else:
    print("No valid schedule found.")