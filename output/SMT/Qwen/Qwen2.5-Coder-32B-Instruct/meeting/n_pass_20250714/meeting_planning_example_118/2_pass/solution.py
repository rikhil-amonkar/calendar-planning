from z3 import *

# Define the variables for the start times of meetings with Richard and Charles
richard_start = Int('richard_start')
charles_start = Int('charles_start')

# Define the constants for the arrival time and meeting durations
arrival_time = 9 * 60  # 9:00 AM in minutes
richard_min_duration = 120  # Minimum duration to meet Richard in minutes
charles_min_duration = 120  # Minimum duration to meet Charles in minutes

# Define the constraints for meeting Richard
richard_constraints = [
    richard_start >= arrival_time,
    richard_start + richard_min_duration <= 13 * 60  # 1:00 PM in minutes
]

# Define the constraints for meeting Charles
charles_constraints = [
    charles_start >= arrival_time,
    charles_start + charles_min_duration <= 13 * 60  # 1:00 PM in minutes
]

# Create solvers for each scenario
richard_solver = Solver()
richard_solver.add(richard_constraints)

charles_solver = Solver()
charles_solver.add(charles_constraints)

# Check if there is a solution for meeting Richard
richard_solution = None
if richard_solver.check() == sat:
    model = richard_solver.model()
    richard_start_time = model[richard_start].as_long()
    richard_start_hour = richard_start_time // 60
    richard_start_minute = richard_start_time % 60
    richard_solution = f"Meet Richard at {richard_start_hour:02}:{richard_start_minute:02} AM for {richard_min_duration} minutes."

# Check if there is a solution for meeting Charles
charles_solution = None
if charles_solver.check() == sat:
    model = charles_solver.model()
    charles_start_time = model[charles_start].as_long()
    charles_start_hour = charles_start_time // 60
    charles_start_minute = charles_start_time % 60
    charles_solution = f"Meet Charles at {charles_start_hour:02}:{charles_start_minute:02} AM for {charles_min_duration} minutes."

# Choose the solution that meets the constraints
if richard_solution and charles_solution:
    # Both solutions are valid, choose one (e.g., the one that starts earlier)
    if richard_start_time < charles_start_time:
        SOLUTION = richard_solution
    else:
        SOLUTION = charles_solution
elif richard_solution:
    SOLUTION = richard_solution
elif charles_solution:
    SOLUTION = charles_solution
else:
    SOLUTION = "No solution found."

print(SOLUTION)