#!/usr/bin/env python3
from z3 import *

# Meeting duration (in minutes)
duration = 30

# Define meeting variables:
# meeting_day: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
meeting_day = Int("meeting_day")
meeting_start = Int("meeting_start")

# Create an Optimize solver to support lexicographic minimization.
opt = Optimize()
# Tell the optimizer to try lexicographic optimization.
opt.set("priority", "lex")

# Allow Monday, Tuesday, or Wednesday.
opt.add(Or(meeting_day == 0, meeting_day == 1, meeting_day == 2))
# Meeting must start between 9:00 and 16:30 (so that it ends by 17:00).
opt.add(meeting_start >= 0, meeting_start + duration <= 480)

# Participants’ busy schedules (times in minutes after 9:00)
robert_busy = {
    0: [(120, 150), (300, 330), (390, 420)],                 # Monday
    1: [(90, 120), (360, 390)],                               # Tuesday
    2: [(60, 120), (150, 180), (210, 240), (270, 300), 
        (360, 390), (420, 450)]                                # Wednesday
}

ralph_busy = {
    0: [(60, 270), (300, 330), (360, 480)],                  # Monday
    1: [(0, 30), (60, 90), (120, 150), (180, 240), 
        (300, 390), (420, 480)],                              # Tuesday
    2: [(90, 120), (150, 180), (240, 330), (450, 480)]         # Wednesday
}

# For each busy interval on a day, add a constraint so that if the meeting falls on that day 
# then it does not overlap the busy period.
def add_busy_constraints(busy_dict):
    for day, intervals in busy_dict.items():
        for (b_start, b_end) in intervals:
            # The meeting does not overlap the busy interval if either 
            # it finishes by the start, or it starts after the busy time.
            opt.add(Implies(meeting_day == day,
                            Or(meeting_start + duration <= b_start,
                               meeting_start >= b_end)))

# Add the busy constraints for both participants.
add_busy_constraints(robert_busy)
add_busy_constraints(ralph_busy)

# Rather than ruling out Monday outright, we “penalize” it.
# Here Tuesday is given a cost of 1, Wednesday a cost of 2, and Monday (which Robert dislikes) gets 1000.
day_cost = If(meeting_day == 1, 1, If(meeting_day == 2, 2, 1000))

# Set our optimization objectives:
# (1) minimize the day‐cost (favor Tuesday, then Wednesday; Monday only if needed)
# (2) then minimize the meeting_start to get the earliest time.
h1 = opt.minimize(day_cost)
h2 = opt.minimize(meeting_start)

# Check for a solution and display the result.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    chosen_start = model[meeting_start].as_long()
    
    # Map numeric day to day names.
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    day_str = day_names.get(chosen_day, "Unknown")
    
    # Convert meeting_start (minutes after 9:00) into HH:MM.
    start_total = 9 * 60 + chosen_start
    start_hour = start_total // 60
    start_minute = start_total % 60
    
    # Meeting end time calculation.
    end_total = start_total + duration
    end_hour = end_total // 60
    end_minute = end_total % 60

    # Print the plan in a friendly format (e.g. "Tuesday: 09:30 to 10:00").
    print(f"{day_str}: {start_hour:02d}:{start_minute:02d} to {end_hour:02d}:{end_minute:02d}")
else:
    print("No available time slot found.")