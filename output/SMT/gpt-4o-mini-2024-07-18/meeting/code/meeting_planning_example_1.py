from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_financial = Real('depart_financial')  # Time at which we leave Richmond District to head to Financial District
arrive_financial = Real('arrive_financial')  # Time at which we arrive at Financial District
depart_betty = Real('depart_betty')  # Time when we leave Financial District after meeting with Betty

# Constants
travel_time_richmond_to_financial = 22  # minutes
travel_time_financial_to_richmond = 21   # minutes
meeting_duration = 60  # minutes
betty_start = 17.25  # 5:15 PM in hours
betty_end = 21.75    # 9:45 PM in hours
arrival_time_richmond = 9.0  # 9:00 AM in hours

# Constraints
solver.add(arrive_financial == depart_financial + travel_time_richmond_to_financial)
solver.add(depart_financial >= arrival_time_richmond)  # Must leave after arriving at Richmond
solver.add(depart_financial <= betty_end - meeting_duration)  # Must leave by this time to meet for 60 minutes
solver.add(arrive_financial >= betty_start)  # Must arrive at or after Betty starts being available
solver.add(depart_betty >= arrive_financial + meeting_duration)  # Must leave after meeting for 60 minutes

# To maximize our meeting time with Betty, we want to meet her until the end of her availability
meet_time = min(depart_betty - arrive_financial, meeting_duration)

# We want to encourage as much meet_time as possible
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_financial_val = model[depart_financial].as_decimal(2)
    arrive_financial_val = model[arrive_financial].as_decimal(2)
    depart_betty_val = model[depart_betty].as_decimal(2)
    
    print(f"Depart from Richmond District to Financial District at: {depart_financial_val} hours")
    print(f"Arrive at Financial District at: {arrive_financial_val} hours")
    print(f"Depart from Financial District after meeting Betty at: {depart_betty_val} hours")
else:
    print("No valid schedule found.")