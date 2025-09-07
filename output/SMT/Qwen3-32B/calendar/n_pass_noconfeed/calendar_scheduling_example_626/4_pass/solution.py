from z3 import *

# Define the solver
solver = Solver()

# Define the time variables for Tuesday
start_tue = Int('start_tue')

# Define the existing meetings for P and J on Tuesday
p_tue_meetings = [(600, 630), (660, 720), (840, 960), (990, 1020)]
j_tue_meetings = [(660, 690), (720, 750), (780, 840), (870, 900), (930, 1020)]

# Add constraints for business hours
solver.add(start_tue >= 540)  # 9 AM
solver.add(start_tue + 60 <= 1020)  # 5 PM

# Check for conflicts with existing meetings
for s, e in p_tue_meetings + j_tue_meetings:
    solver.add(Or(start_tue + 60 <= s, start_tue >= e))

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    start_time = model[start_tue].as_long()
    end_time = start_time + 60
    start_h, start_m = divmod(start_time, 60)
    end_h, end_m = divmod(end_time, 60)
    print(f"{start_h:02}:{start_m:02}:{end_h:02}:{end_m:02} Tuesday")