from z3 import Solver, Int, Or, sat

# Meeting parameters.
duration = 30  # meeting duration in minutes
WORK_START = 9 * 60   # 9:00 AM in minutes
WORK_END   = 17 * 60  # 17:00 in minutes

# Days encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Busy intervals (in minutes) for Frank.
# Each interval is [start, end)
frank_busy = {
    1: [(11 * 60, 11 * 60 + 30),   # Tuesday: 11:00-11:30
        (12 * 60 + 30, 13 * 60)],   # Tuesday: 12:30-13:00
    2: [(10 * 60, 10 * 60 + 30)],    # Wednesday: 10:00-10:30
    3: [(12 * 60 + 30, 13 * 60)],    # Thursday: 12:30-13:00
    4: [(13 * 60 + 30, 14 * 60),     # Friday: 13:30-14:00
        (15 * 60 + 30, 16 * 60)]     # Friday: 15:30-16:00
}

# Busy intervals (in minutes) for Diana.
# Each interval is [start, end)
diana_busy = {
    0: [(9 * 60, 11 * 60 + 30),    # Monday: 9:00-11:30
        (12 * 60 + 30, 13 * 60),   # Monday: 12:30-13:00
        (14 * 60, 15 * 60),        # Monday: 14:00-15:00
        (16 * 60, 16 * 60 + 30)],   # Monday: 16:00-16:30
    1: [(9 * 60 + 30, 10 * 60),    # Tuesday: 9:30-10:00
        (10 * 60 + 30, 12 * 60),   # Tuesday: 10:30-12:00
        (14 * 60, 14 * 60 + 30)],   # Tuesday: 14:00-14:30
    2: [(10 * 60, 10 * 60 + 30),   # Wednesday: 10:00-10:30
        (11 * 60 + 30, 12 * 60 + 30),# Wednesday: 11:30-12:30
        (14 * 60, 14 * 60 + 30),    # Wednesday: 14:00-14:30
        (16 * 60, 16 * 60 + 30)],   # Wednesday: 16:00-16:30
    3: [(9 * 60, 11 * 60 + 30),    # Thursday: 9:00-11:30
        (12 * 60, 13 * 60),        # Thursday: 12:00-13:00
        (13 * 60 + 30, 15 * 60),    # Thursday: 13:30-15:00
        (15 * 60 + 30, 17 * 60)],   # Thursday: 15:30-17:00
    4: [(10 * 60, 10 * 60 + 30),   # Friday: 10:00-10:30
        (11 * 60, 12 * 60 + 30),   # Friday: 11:00-12:30
        (14 * 60, 16 * 60)]        # Friday: 14:00-16:00
}

# Constraints from preferences:
# Diana does not want to meet on Tuesday and Thursday.
# Also, we want to schedule the meeting at the earliest availability.
# Thus, we will only consider days that are acceptable to Diana:
# Allowed days: Monday (0), Wednesday (2), Friday (4)
primary_days = [0, 2, 4]

# In case no solution is found on the preferred days, we can try backup days.
backup_days = [1, 3]

def no_overlap(busy_start, busy_end, s, duration):
    # Ensures that the meeting (from s to s+duration) does not overlap with a busy interval.
    return Or(s + duration <= busy_start, s >= busy_end)

def find_earliest_meeting_time(candidate_days):
    # Iterate over candidate days in order.
    for day in candidate_days:
        solver = Solver()
        # Define meeting start time variable in minutes from midnight.
        s = Int("s")
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add constraints for Frank's busy intervals.
        if day in frank_busy:
            for busy_start, busy_end in frank_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Add constraints for Diana's busy intervals.
        if day in diana_busy:
            for busy_start, busy_end in diana_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Since we want the earliest availability, try start times in ascending order.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

# First, try the preferred (primary) days.
day, t = find_earliest_meeting_time(primary_days)

# If no solution is found on the primary days, try the backup days.
if day is None:
    day, t = find_earliest_meeting_time(backup_days)

if day is not None and t is not None:
    meeting_end = t + duration
    start_hr, start_min = divmod(t, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".
          format(day_names[day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")