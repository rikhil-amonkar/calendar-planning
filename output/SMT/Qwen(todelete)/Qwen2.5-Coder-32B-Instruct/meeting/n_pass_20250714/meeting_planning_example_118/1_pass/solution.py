from z3 import *

# Define the variables for the start times of meetings with Richard and Charles
richard_start = Int('richard_start')
charles_start = Int('charles_start')

# Define the constants for the arrival time and meeting durations
arrival_time = 9 * 60  # 9:00 AM in minutes
richard_min_duration = 120  # Minimum duration to meet Richard in minutes
charles_min_duration = 120  # Minimum duration to meet Charles in minutes

# Define the constraints
constraints = [
    # You must arrive at Bayview at 9:00 AM
    richard_start >= arrival_time,
    charles_start >= arrival_time,

    # Richard is available from 8:45 AM to 1:00 PM
    richard_start <= 13 * 60 - richard_min_duration,  # 1:00 PM in minutes minus the minimum duration

    # Charles is available from 9:45 AM to 1:00 PM
    charles_start <= 13 * 60 - charles_min_duration,  # 1:00 PM in minutes minus the minimum duration

    # Travel times between locations
    # If you meet Richard first, you must be able to travel to Charles within his availability
    Or(
        And(
            richard_start + richard_min_duration + 24 <= charles_start,  # Travel from Union Square to Presidio
            charles_start + charles_min_duration <= 13 * 60
        ),
        # If you meet Charles first, you must be able to travel to Richard within his availability
        And(
            charles_start + charles_min_duration + 31 <= richard_start,  # Travel from Presidio to Union Square
            richard_start + richard_min_duration <= 13 * 60
        )
    )
]

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    richard_start_time = model[richard_start].as_long()
    charles_start_time = model[charles_start].as_long()

    # Convert start times back to hours and minutes
    richard_start_hour = richard_start_time // 60
    richard_start_minute = richard_start_time % 60
    charles_start_hour = charles_start_time // 60
    charles_start_minute = charles_start_time % 60

    SOLUTION = f"Meet Richard at {richard_start_hour:02}:{richard_start_minute:02} AM/PM for {richard_min_duration} minutes.\n"
    SOLUTION += f"Meet Charles at {charles_start_hour:02}:{charles_start_minute:02} AM/PM for {charles_min_duration} minutes."
else:
    SOLUTION = "No solution found."

print(SOLUTION)