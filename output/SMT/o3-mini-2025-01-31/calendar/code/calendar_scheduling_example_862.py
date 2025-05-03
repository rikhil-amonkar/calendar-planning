from z3 import Solver, Int, Or, sat

# Meeting duration: 1 hour = 60 minutes
duration = 60

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60    # 540
WORK_END   = 17 * 60   # 1020

# Days encoded as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# The group would like to meet at their earliest availability, so we check the days in order.
candidate_days = [0, 1, 2, 3]

# Busy schedules for Ann (in minutes from midnight)
ann_busy = {
    0: [ (10 * 60 + 30, 11 * 60),    # Monday: 10:30-11:00
         (12 * 60, 12 * 60 + 30),     # Monday: 12:00-12:30
         (15 * 60 + 30, 16 * 60) ],   # Monday: 15:30-16:00
    1: [ (9 * 60, 9 * 60 + 30),      # Tuesday: 9:00-9:30
         (13 * 60, 13 * 60 + 30),     # Tuesday: 13:00-13:30
         (16 * 60 + 30, 17 * 60) ],   # Tuesday: 16:30-17:00
    2: [ (9 * 60 + 30, 11 * 60),     # Wednesday: 9:30-11:00
         (12 * 60 + 30, 14 * 60),     # Wednesday: 12:30-14:00
         (15 * 60 + 30, 16 * 60) ],   # Wednesday: 15:30-16:00
    3: [ (10 * 60, 10 * 60 + 30) ]    # Thursday: 10:00-10:30
}

# Busy schedules for Amanda (in minutes from midnight)
amanda_busy = {
    0: [ (9 * 60, 10 * 60),         # Monday: 9:00-10:00
         (10 * 60 + 30, 11 * 60),    # Monday: 10:30-11:00
         (11 * 60 + 30, 12 * 60),    # Monday: 11:30-12:00
         (13 * 60, 14 * 60 + 30) ],  # Monday: 13:00-14:30
    1: [ (9 * 60, 9 * 60 + 30),      # Tuesday: 9:00-9:30
         (10 * 60 + 30, 11 * 60),    # Tuesday: 10:30-11:00
         (12 * 60, 12 * 60 + 30),    # Tuesday: 12:00-12:30
         (13 * 60, 13 * 60 + 30),    # Tuesday: 13:00-13:30
         (16 * 60, 17 * 60) ],       # Tuesday: 16:00-17:00
    2: [ (9 * 60, 16 * 60),         # Wednesday: 9:00-16:00
         (16 * 60 + 30, 17 * 60) ],  # Wednesday: 16:30-17:00
    3: [ (9 * 60 + 30, 10 * 60),     # Thursday: 9:30-10:00
         (10 * 60 + 30, 12 * 60 + 30),# Thursday: 10:30-12:30
         (13 * 60, 14 * 60),         # Thursday: 13:00-14:00
         (14 * 60 + 30, 15 * 60 + 30),# Thursday: 14:30-15:30
         (16 * 60 + 30, 17 * 60) ]    # Thursday: 16:30-17:00
}

# Helper function to ensure the meeting does NOT overlap with a busy interval.
def no_overlap(busy_start, busy_end, s):
    # The meeting [s, s+duration) must finish on or before the busy interval starts,
    # or start on or after the busy interval ends.
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find the earliest available meeting time across candidate days.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time (in minutes from midnight)
        
        # The meeting must lie within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Ann's busy constraints for the day.
        for busy_interval in ann_busy.get(day, []):
            busy_start, busy_end = busy_interval
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Add Amanda's busy constraints for the day.
        for busy_interval in amanda_busy.get(day, []):
            busy_start, busy_end = busy_interval
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Iterate minute-by-minute to choose the earliest valid start time.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

selected_day, selected_start = find_meeting_time(candidate_days)

if selected_day is not None:
    selected_end = selected_start + duration
    # Convert the minutes into HH:MM format:
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")