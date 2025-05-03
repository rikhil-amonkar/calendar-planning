from z3 import Solver, Int, Or, sat

# Meeting parameters.
duration = 60  # meeting duration in minutes (1 hour)
WORK_START = 9 * 60    # 9:00 AM in minutes
WORK_END   = 17 * 60   # 17:00 in minutes

# Days encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Bryan's busy intervals.
# Each busy interval is expressed as (start, end) with times in minutes.
bryan_busy = {
    3: [(9 * 60 + 30, 10 * 60),   # Thursday: 9:30-10:00
        (12 * 60 + 30, 13 * 60)],  # Thursday: 12:30-13:00
    4: [(10 * 60 + 30, 11 * 60),   # Friday: 10:30-11:00
        (14 * 60, 14 * 60 + 30)]   # Friday: 14:00-14:30
}
# Bryan has no busy intervals on Monday, Tuesday, or Wednesday per given data.

# Nicholas's busy intervals.
nicholas_busy = {
    0: [(11 * 60 + 30, 12 * 60),   # Monday: 11:30-12:00
        (13 * 60, 15 * 60 + 30)],  # Monday: 13:00-15:30
    1: [(9 * 60, 9 * 60 + 30),     # Tuesday: 9:00-9:30
        (11 * 60, 13 * 60 + 30),   # Tuesday: 11:00-13:30
        (14 * 60, 16 * 60 + 30)],   # Tuesday: 14:00-16:30
    2: [(9 * 60, 9 * 60 + 30),     # Wednesday: 9:00-9:30
        (10 * 60, 11 * 60),        # Wednesday: 10:00-11:00
        (11 * 60 + 30, 13 * 60 + 30),  # Wednesday: 11:30-13:30
        (14 * 60, 14 * 60 + 30),    # Wednesday: 14:00-14:30
        (15 * 60, 16 * 60 + 30)],   # Wednesday: 15:00-16:30
    3: [(10 * 60 + 30, 11 * 60 + 30),  # Thursday: 10:30-11:30
        (12 * 60, 12 * 60 + 30),       # Thursday: 12:00-12:30
        (15 * 60, 15 * 60 + 30),       # Thursday: 15:00-15:30
        (16 * 60 + 30, 17 * 60)],       # Thursday: 16:30-17:00
    4: [(9 * 60, 10 * 60 + 30),    # Friday: 9:00-10:30
        (11 * 60, 12 * 60),        # Friday: 11:00-12:00
        (12 * 60 + 30, 14 * 60 + 30),  # Friday: 12:30-14:30
        (15 * 60 + 30, 16 * 60),    # Friday: 15:30-16:00
        (16 * 60 + 30, 17 * 60)]    # Friday: 16:30-17:00
}

# Preferences:
# Bryan would like to avoid more meetings on Tuesday (day 1).
# Nicholas would rather not meet on Monday (day 0) or Thursday (day 3).
#
# To respect these preferences as much as possible, we define primary candidate days as those
# that are not avoided by either participant. That leaves Wednesday (2) and Friday (4) as primary.
#
# The backup candidate days are the remaining days: Monday (0), Tuesday (1), Thursday (3).

primary_days = [2, 4]  # Wednesday and Friday (preferred by both)
backup_days = [0, 1, 3]  # Monday, Tuesday, and Thursday (less preferred)

def no_overlap(busy_start, busy_end, s, dur):
    # Returns a constraint ensuring the meeting (starting at s with duration dur)
    # does not overlap with the busy interval [busy_start, busy_end).
    return Or(s + dur <= busy_start, s >= busy_end)

def find_earliest_meeting(candidate_days):
    # Try the candidate days in the given order.
    for day in candidate_days:
        solver = Solver()
        s = Int("s")  # meeting start time variable (in minutes)
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add participant busy constraints for this day if any.
        if day in bryan_busy:
            for busy_start, busy_end in bryan_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        if day in nicholas_busy:
            for busy_start, busy_end in nicholas_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # For preferred days we don't need extra restrictions.
        # (Days in backup are attempted later.)
        
        # Search for the earliest feasible start time by iterating through possible minutes.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

# First try the primary candidate days (Wednesday and Friday).
day, t = find_earliest_meeting(primary_days)

# If no solution is found on primary days, then try backup days.
if day is None:
    day, t = find_earliest_meeting(backup_days)
    
if day is not None and t is not None:
    meeting_end = t + duration
    start_hr, start_min = divmod(t, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".
          format(day_names[day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")