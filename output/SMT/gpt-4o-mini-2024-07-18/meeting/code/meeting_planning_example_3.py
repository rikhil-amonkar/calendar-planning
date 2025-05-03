from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_golden_gate = Real('depart_golden_gate')  # Time at which we leave Bayview to head to Golden Gate Park
arrive_golden_gate = Real('arrive_golden_gate')  # Time at which we arrive at Golden Gate Park
depart_barbara = Real('depart_barbara')  # Time we leave Golden Gate Park after meeting with Barbara

# Constants
travel_time_bayview_to_golden_gate = 22  # minutes
travel_time_golden_gate_to_bayview = 23   # minutes
meeting_duration = 90  # minutes
barbara_start = 8.0    # 8:00 AM in hours
barbara_end = 11.5     # 11:30 AM in hours
arrival_time_bayview = 9.0  # 9:00 AM in hours

# Constraints
solver.add(arrive_golden_gate == depart_golden_gate + travel_time_bayview_to_golden_gate)
solver.add(depart_golden_gate >= arrival_time_bayview)  # Must leave after arriving at Bayview
solver.add(depart_golden_gate <= barbara_end - meeting_duration)  # Must leave in time to meet for 90 minutes
solver.add(arrive_golden_gate >= barbara_start)  # Must arrive at or after Barbara starts being available
solver.add(depart_barbara >= arrive_golden_gate + meeting_duration)  # Must leave after meeting for 90 minutes

# Maximize the meeting time with Barbara (ideally want to meet her for 90 minutes)
meet_time = min(depart_barbara - arrive_golden_gate, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_golden_gate_val = model[depart_golden_gate].as_decimal(2)
    arrive_golden_gate_val = model[arrive_golden_gate].as_decimal(2)
    depart_barbara_val = model[depart_barbara].as_decimal(2)
    
    print(f"Depart from Bayview to Golden Gate Park at: {depart_golden_gate_val} hours")
    print(f"Arrive at Golden Gate Park at: {arrive_golden_gate_val} hours")
    print(f"Depart from Golden Gate Park after meeting Barbara at: {depart_barbara_val} hours")
else:
    print("No valid schedule found.")