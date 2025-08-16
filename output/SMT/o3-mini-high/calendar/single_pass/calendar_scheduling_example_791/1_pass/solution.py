from z3 import *

def minutes_to_time(m):
    # Converts minutes since midnight to HH:MM format.
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Create a solver instance
s = Solver()

# Define the variables:
# day: 0 = Monday, 1 = Tuesday, 2 = Wednesday
day = Int('day')
# start: meeting start time in minutes from midnight
start = Int('start')
duration = 30  # meeting duration in minutes

# Working hours: meeting must be between 9:00 (540 min) and 17:00 (1020 min)
s.add(start >= 540, start + duration <= 1020)

# The meeting can only be scheduled on Monday, Tuesday, or Wednesday.
s.add(Or(day == 0, day == 1, day == 2))

# Busy slots for Nicole (all times in minutes)
busy_nicole = {
    0: [(540, 570),    # Monday: 9:00 - 9:30
        (780, 810),    # Monday: 13:00 - 13:30
        (870, 930)],   # Monday: 14:30 - 15:30
    1: [(540, 570),    # Tuesday: 9:00 - 9:30
        (690, 810),    # Tuesday: 11:30 - 13:30
        (870, 930)],   # Tuesday: 14:30 - 15:30
    2: [(600, 660),    # Wednesday: 10:00 - 11:00
        (750, 900),    # Wednesday: 12:30 - 15:00
        (960, 1020)]   # Wednesday: 16:00 - 17:00
}

# Busy slots for Ruth
busy_ruth = {
    0: [(540, 1020)],   # Monday: 9:00 - 17:00
    1: [(540, 1020)],   # Tuesday: 9:00 - 17:00
    2: [(540, 630),     # Wednesday: 9:00 - 10:30
        (660, 690),     # Wednesday: 11:00 - 11:30
        (720, 750),     # Wednesday: 12:00 - 12:30
        (810, 930),     # Wednesday: 13:30 - 15:30
        (960, 990)]     # Wednesday: 16:00 - 16:30
}

# A helper function to add the non-overlap constraints:
# If a meeting is scheduled on a given day, it must not overlap with the busy interval.
def add_busy_constraints(solver, day_var, start_var, meeting_duration, busy_slots):
    for d, intervals in busy_slots.items():
        for (b_start, b_end) in intervals:
            # Either the meeting ends before the busy interval starts,
            # or it starts after the busy interval ends.
            solver.add(Implies(day_var == d, Or(start_var + meeting_duration <= b_start, start_var >= b_end)))

# Add constraints for Nicole and Ruth.
add_busy_constraints(s, day, start, duration, busy_nicole)
add_busy_constraints(s, day, start, duration, busy_ruth)

# Additional preference: Ruth does not want to meet on Wednesday after 13:30.
# We interpret this as: if the meeting is on Wednesday then it must finish by 13:30 (810 minutes).
s.add(Implies(day == 2, start + duration <= 810))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    chosen_day = m[day].as_long()
    chosen_start = m[start].as_long()
    chosen_end = chosen_start + duration
    
    # Map our day numbers to the day names.
    day_map = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    day_name = day_map[chosen_day]
    
    # Output the solution in the required format.
    print("SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {minutes_to_time(chosen_start)}")
    print(f"End Time: {minutes_to_time(chosen_end)}")
else:
    print("No solution found.")