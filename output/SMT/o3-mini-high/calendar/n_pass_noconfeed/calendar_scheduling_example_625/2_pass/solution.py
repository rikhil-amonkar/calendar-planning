#!/usr/bin/env python3
import z3

# Define meeting duration in minutes.
MEETING_DURATION = 30

# Define minutes from midnight for work hours.
WORK_START = 9 * 60    # 09:00 => 540
WORK_END = 17 * 60     # 17:00 => 1020
LATEST_START = WORK_END - MEETING_DURATION  # Latest possible start

# Define day codes: 0 for Monday, 1 for Tuesday.
monday, tuesday = 0, 1

# Create an optimizer instance (we need Optimize for soft constraints).
solver = z3.Optimize()

# Define variables: meeting start time (in minutes) and day.
start = z3.Int('start')  # Start time in minutes from midnight.
day = z3.Int('day')      # 0: Monday, 1: Tuesday

# The meeting must be within work hours.
solver.add(start >= WORK_START, start <= LATEST_START)

# The meeting must be scheduled on either Monday or Tuesday (using z3.Or).
solver.add(z3.Or(day == monday, day == tuesday))

# Harold's blocked times and his preferences:

# For Monday:
#   Harold is busy from 9:00-10:00 and 10:30-17:00.
#   Thus, the only possible Monday slot is exactly 10:00 to 10:30.
solver.add(z3.Implies(day == monday,
                        z3.And(start >= 10 * 60, start + MEETING_DURATION <= 10 * 60 + 30)))

# For Tuesday:
#   Harold is busy during:
#     9:00-9:30, 10:30-11:30, 12:30-13:30, 14:30-15:30, and 16:00-17:00.
#   He would like to avoid any meeting on Tuesday that starts before 14:30.
#   This leaves only a single valid option: 15:30 to 16:00.
solver.add(z3.Implies(day == tuesday,
                        z3.And(start >= 15 * 60 + 30, start + MEETING_DURATION <= 16 * 60)))

# Preference: Harold would like to avoid more meetings on Monday.
# We add a soft constraint to prefer Tuesday.
solver.add_soft(day == tuesday)

# Check for a solution.
if solver.check() == z3.sat:
    model = solver.model()
    chosen_day = model[day].as_long()
    chosen_start = model[start].as_long()
    meeting_end = chosen_start + MEETING_DURATION

    # Convert minutes into HH:MM format.
    def minutes_to_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    start_str = minutes_to_str(chosen_start)
    end_str = minutes_to_str(meeting_end)
    day_str = "Monday" if chosen_day == monday else "Tuesday"

    # Output the meeting time and day.
    print(f"{start_str}:{end_str} {day_str}")
else:
    print("No valid meeting time found.")