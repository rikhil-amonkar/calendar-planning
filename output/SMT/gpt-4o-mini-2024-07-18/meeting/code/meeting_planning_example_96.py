from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_nob = Real('depart_nob')        # Time you leave Sunset District to head to Nob Hill
arrive_nob = Real('arrive_nob')        # Time you arrive at Nob Hill
depart_rebecca = Real('depart_rebecca') # Time you leave Nob Hill after meeting Rebecca

# Constants
travel_time_sunset_to_nob = 27         # minutes from Sunset District to Nob Hill
travel_time_nob_to_sunset = 25          # minutes from Nob Hill back to Sunset District
meeting_duration = 30                    # minimum meeting duration (in minutes)
rebecca_start = 9.0                     # 9:00 AM in hours
rebecca_end = 18.25                     # 6:15 PM in hours
arrival_time_sunset = 9.0                # 9:00 AM in hours

# Constraints
solver.add(arrive_nob == depart_nob + travel_time_sunset_to_nob)  # Arrival time at Nob Hill
solver.add(depart_nob >= arrival_time_sunset)                       # Must leave after arriving at Sunset District
solver.add(depart_nob <= rebecca_end - (meeting_duration / 60))    # Must leave in time to meet for 30 minutes
solver.add(arrive_nob >= rebecca_start)                             # Must arrive at or after Rebecca starts being available
solver.add(depart_rebecca >= arrive_nob + (meeting_duration / 60)) # Must leave after meeting for 30 minutes

# Maximize the meeting time with Rebecca (ideally want to meet her for at least 30 minutes)
meet_time = min(depart_rebecca - arrive_nob, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_nob_val = model[depart_nob].as_decimal(2)
    arrive_nob_val = model[arrive_nob].as_decimal(2)
    depart_rebecca_val = model[depart_rebecca].as_decimal(2)

    print(f"Depart from Sunset District to Nob Hill at: {depart_nob_val} hours")
    print(f"Arrive at Nob Hill at: {arrive_nob_val} hours")
    print(f"Depart from Nob Hill after meeting Rebecca at: {depart_rebecca_val} hours")
else:
    print("No valid schedule found.")