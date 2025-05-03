from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_russian = Real('depart_russian')  # Time you leave Alamo Square to head to Russian Hill
arrive_russian = Real('arrive_russian')  # Time you arrive at Russian Hill
depart_james = Real('depart_james')      # Time you leave Russian Hill after meeting James

# Constants
travel_time_alamo_to_russian = 13       # minutes from Alamo Square to Russian Hill
travel_time_russian_to_alamo = 15        # minutes from Russian Hill to Alamo Square
meeting_duration = 15                     # minimum meeting duration (in minutes)
james_start = 11 + 15 / 60               # 11:15 AM in hours
james_end = 12.0                         # 12:00 PM in hours
arrival_time_alamo = 9.0                  # 9:00 AM in hours

# Constraints
solver.add(arrive_russian == depart_russian + travel_time_alamo_to_russian)  # Arrival time at Russian Hill
solver.add(depart_russian >= arrival_time_alamo)  # Must leave after arriving at Alamo Square
solver.add(depart_russian <= james_end - (meeting_duration / 60))  # Must leave in time to meet for 15 minutes
solver.add(arrive_russian >= james_start)  # Must arrive at or after James starts being available
solver.add(depart_james >= arrive_russian + (meeting_duration / 60))  # Must leave after meeting for 15 minutes

# Maximize the meeting time with James (ideally we want to meet him for at least 15 minutes)
meet_time = min(depart_james - arrive_russian, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_russian_val = model[depart_russian].as_decimal(2)
    arrive_russian_val = model[arrive_russian].as_decimal(2)
    depart_james_val = model[depart_james].as_decimal(2)

    print(f"Depart from Alamo Square to Russian Hill at: {depart_russian_val} hours")
    print(f"Arrive at Russian Hill at: {arrive_russian_val} hours")
    print(f"Depart from Russian Hill after meeting James at: {depart_james_val} hours")
else:
    print("No valid schedule found.")