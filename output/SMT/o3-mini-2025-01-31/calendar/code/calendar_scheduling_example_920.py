from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (1 hour)
WORK_START = 9 * 60   # 9:00 AM in minutes (540)
WORK_END = 17 * 60    # 17:00 in minutes (1020)

# Day encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Charles' busy intervals (in minutes)
# Only days with specified busy intervals are listed.
charles_busy = {
    1: [ (10 * 60, 11 * 60),    # Tuesday: 10:00 to 11:00
         (13 * 60, 14 * 60),    # Tuesday: 13:00 to 14:00
         (15 * 60, 16 * 60) ],  # Tuesday: 15:00 to 16:00
    2: [ (12 * 60, 12 * 60 + 30) ],  # Wednesday: 12:00 to 12:30
    3: [ (16 * 60 + 30, 17 * 60) ],  # Thursday: 16:30 to 17:00
    4: [ (10 * 60 + 30, 11 * 60 + 30),  # Friday: 10:30 to 11:30
         (12 * 60 + 30, 13 * 60),        # Friday: 12:30 to 13:00
         (15 * 60 + 30, 16 * 60) ]        # Friday: 15:30 to 16:00
}

# Lori's busy intervals (in minutes)
lori_busy = {
    0: [ (9 * 60, 9 * 60 + 30),     # Monday: 9:00 to 9:30
         (10 * 60, 11 * 60 + 30),   # Monday: 10:00 to 11:30
         (12 * 60, 13 * 60 + 30),   # Monday: 12:00 to 13:30
         (14 * 60, 17 * 60) ],      # Monday: 14:00 to 17:00
    1: [ (9 * 60, 10 * 60 + 30),    # Tuesday: 9:00 to 10:30
         (11 * 60, 15 * 60 + 30),   # Tuesday: 11:00 to 15:30
         (16 * 60, 17 * 60) ],      # Tuesday: 16:00 to 17:00
    2: [ (9 * 60 + 30, 13 * 60 + 30),  # Wednesday: 9:30 to 13:30
         (14 * 60 + 30, 16 * 60 + 30) ],# Wednesday: 14:30 to 16:30
    3: [ (9 * 60, 13 * 60),         # Thursday: 9:00 to 13:00
         (14 * 60 + 30, 16 * 60 + 30) ],# Thursday: 14:30 to 16:30
    4: [ (9 * 60, 11 * 60 + 30),     # Friday: 9:00 to 11:30
         (12 * 60, 17 * 60) ]        # Friday: 12:00 to 17:00
}

# Helper function to ensure no overlap between meeting time and a busy interval.
def no_overlap(busy_start, busy_end, s, duration):
    # Meeting (from s to s+duration) must either finish before busy_start,
    # or start after busy_end.
    return Or(s + duration <= busy_start, s >= busy_end)

def find_earliest_meeting(days):
    # Process each day in order for earliest availability
    for day in days:
        solver = Solver()
        s = Int("s")  # start time in minutes from midnight
        
        # Meeting must be scheduled during work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Charles' busy constraints for the day, if any.
        if day in charles_busy:
            for bs, be in charles_busy[day]:
                solver.add(no_overlap(bs, be, s, duration))
        
        # Add Lori's busy constraints for the day, if any.
        if day in lori_busy:
            for bs, be in lori_busy[day]:
                solver.add(no_overlap(bs, be, s, duration))
        
        # Check each minute within work hours for a valid time slot.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

# Order of days: Monday (0), Tuesday (1), Wednesday (2), Thursday (3), Friday (4)
allowed_days = [0, 1, 2, 3, 4]

day, start_time = find_earliest_meeting(allowed_days)

if day is not None and start_time is not None:
    meeting_end = start_time + duration
    start_hr, start_min = divmod(start_time, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
          day_names[day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")