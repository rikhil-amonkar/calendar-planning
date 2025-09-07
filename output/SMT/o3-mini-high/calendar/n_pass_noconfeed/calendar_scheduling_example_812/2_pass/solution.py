#!/usr/bin/env python3
from z3 import Optimize, Int, Or, Implies, sat, unknown

# Meeting and working hours configuration
meeting_duration = 30    # in minutes
work_start = 0           # 9:00 corresponds to 0 minutes
work_end = 480           # 17:00 corresponds to 480 minutes after 9:00

# Day indices: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}

# Create SMT variables:
# "day" represents the chosen day (0 to 3)
# "start" represents the meeting start time in minutes offset from 9:00.
day = Int('day')
start = Int('start')

# Create the Z3 optimizer
opt = Optimize()

# Add basic domain constraints
opt.add(day >= 0, day <= 3)
opt.add(start >= work_start, start <= work_end - meeting_duration)

# Define the participants' blocked intervals.
# The times are offsets in minutes from 9:00.
mary_blocks = {
    0: [],  # Monday: no meetings
    1: [(60, 90), (390, 420)],       # Tuesday: 10:00–10:30, 15:30–16:00
    2: [(30, 60), (360, 390)],        # Wednesday: 9:30–10:00, 15:00–15:30
    3: [(0, 60), (90, 150)]           # Thursday: 9:00–10:00, 10:30–11:30
}

alexis_blocks = {
    0: [(0, 60), (90, 180), (210, 450)],                    # Monday: 9:00–10:00, 10:30–12:00, 12:30–16:30
    1: [(0, 60), (90, 150), (180, 390), (420, 480)],         # Tuesday: 9:00–10:00, 10:30–11:30, 12:00–15:30, 16:00–17:00
    2: [(0, 120), (150, 480)],                              # Wednesday: 9:00–11:00, 11:30–17:00
    3: [(60, 180), (300, 330), (390, 420), (450, 480)]       # Thursday: 10:00–12:00, 14:00–14:30, 15:30–16:00, 16:30–17:00
}

# Helper function: returns the constraint that a meeting starting at s
# (lasting meeting_duration minutes) does not overlap a blocked interval.
def no_overlap(s, block_start, block_end):
    # The meeting must finish before the block starts OR start after the block ends.
    return Or(s + meeting_duration <= block_start, s >= block_end)

# Add constraints so that if the meeting is scheduled on day d it does not overlap Mary’s blocks.
for d in range(4):
    for (b_start, b_end) in mary_blocks[d]:
        opt.add(Implies(day == d, no_overlap(start, b_start, b_end)))

# Add constraints so that if the meeting is scheduled on day d it does not overlap Alexis’s blocks.
for d in range(4):
    for (b_start, b_end) in alexis_blocks[d]:
        opt.add(Implies(day == d, no_overlap(start, b_start, b_end)))

# Optimize for the earliest availability: first minimize day, then the start time.
opt.minimize(day)
opt.minimize(start)

# Call check() once and use its result
result = opt.check()
if result == sat or result == unknown:
    model = opt.model()
    chosen_day   = model[day].as_long()
    chosen_start = model[start].as_long()

    # Convert the chosen start time to actual clock time.
    # 0 corresponds to 9:00. Thus, add 9 to the computed hours.
    start_hour = 9 + (chosen_start // 60)
    start_min  = chosen_start % 60

    meeting_end = chosen_start + meeting_duration
    end_hour = 9 + (meeting_end // 60)
    end_min  = meeting_end % 60

    # Format the meeting time as HH:MM:HH:MM and include the day.
    time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
    print(f"{day_names[chosen_day]} {time_str}")
else:
    print("No valid meeting time found.")