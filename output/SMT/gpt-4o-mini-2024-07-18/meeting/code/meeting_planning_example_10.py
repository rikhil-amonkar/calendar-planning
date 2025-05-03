from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_marina = Real('depart_marina')  # Time at which we leave Golden Gate Park to head to Marina District
arrive_marina = Real('arrive_marina')  # Time at which we arrive at Marina District
depart_james = Real('depart_james')  # Time we leave Marina District after meeting with James

# Constants
travel_time_golden_gate_to_marina = 16  # minutes
travel_time_marina_to_golden_gate = 18   # minutes
meeting_duration = 15  # minutes
james_start = 10.25    # 10:15 AM in hours
james_end = 13.5       # 1:30 PM in hours
arrival_time_golden_gate = 9.0  # 9:00 AM in hours

# Constraints
solver.add(arrive_marina == depart_marina + travel_time_golden_gate_to_marina)
solver.add(depart_marina >= arrival_time_golden_gate)  # Must leave after arriving at Golden Gate Park
solver.add(depart_marina <= james_end - meeting_duration)  # Must meet James for at least 15 minutes
solver.add(arrive_marina >= james_start)  # Must arrive at or after James starts being available
solver.add(depart_james >= arrive_marina + meeting_duration)  # Must leave after meeting for 15 minutes

# Maximize the meeting time with James (ideally want to meet him for 15 minutes)
meet_time = min(depart_james - arrive_marina, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_marina_val = model[depart_marina].as_decimal(2)
    arrive_marina_val = model[arrive_marina].as_decimal(2)
    depart_james_val = model[depart_james].as_decimal(2)
    
    print(f"Depart from Golden Gate Park to Marina District at: {depart_marina_val} hours")
    print(f"Arrive at Marina District at: {arrive_marina_val} hours")
    print(f"Depart from Marina District after meeting James at: {depart_james_val} hours")
else:
    print("No valid schedule found.")