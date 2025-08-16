from z3 import *

# Meeting details
duration = 30  # in minutes
# Working hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# So meeting start must be between 540 and 990 (since 990 + 30 = 1020)

# Create the solver
s = Solver()

# day: 0 = Monday, 1 = Tuesday, 2 = Wednesday
day = Int('day')
start = Int('start')  # meeting start time in minutes from midnight

# Domain constraints
s.add(Or(day == 0, day == 1, day == 2))
s.add(start >= 540, start <= 990)

# John's preference: if meeting on Monday, avoid meetings after 14:30.
# That means the meeting must finish by 14:30 (870 minutes), so start must be <= 840.
s.add(If(day == 0, start <= 840, True))

# A helper for non-overlap: For a busy interval [busy_start, busy_end],
# the meeting [start, start + duration] must either finish before busy_start or start at/after busy_end.
def no_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Jennifer's schedule constraints:

# Monday (day == 0)
# Busy intervals:
#   09:00-11:00  -> [540, 660]
#   11:30-13:00  -> [690, 780]
#   13:30-14:30  -> [810, 870]
#   15:00-17:00  -> [900, 1020]
monday_busy = And(
    no_overlap(540, 660),
    no_overlap(690, 780),
    no_overlap(810, 870),
    no_overlap(900, 1020)
)
s.add(If(day == 0, monday_busy, True))

# Tuesday (day == 1)
# Busy intervals:
#   09:00-11:30  -> [540, 690]
#   12:00-17:00  -> [720, 1020]
tuesday_busy = And(
    no_overlap(540, 690),
    no_overlap(720, 1020)
)
s.add(If(day == 1, tuesday_busy, True))

# Wednesday (day == 2)
# Busy intervals:
#   09:00-11:30  -> [540, 690]
#   12:00-12:30  -> [720, 750]
#   13:00-14:00  -> [780, 840]
#   14:30-16:00  -> [870, 960]
#   16:30-17:00  -> [990, 1020]
wednesday_busy = And(
    no_overlap(540, 690),
    no_overlap(720, 750),
    no_overlap(780, 840),
    no_overlap(870, 960),
    no_overlap(990, 1020)
)
s.add(If(day == 2, wednesday_busy, True))

# Check for a solution.
if s.check() == sat:
    model = s.model()
    chosen_day = model[day].as_long()
    chosen_start = model[start].as_long()
    chosen_end = chosen_start + duration

    # Map the day integer to its name.
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    day_str = day_names[chosen_day]

    # Function to convert minutes (from midnight) to HH:MM (24-hour) format.
    def minutes_to_time(m):
        h = m // 60
        m = m % 60
        return f"{h:02d}:{m:02d}"

    start_time_str = minutes_to_time(chosen_start)
    end_time_str = minutes_to_time(chosen_end)

    # Output in the required format.
    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")
else:
    print("No solution found.")