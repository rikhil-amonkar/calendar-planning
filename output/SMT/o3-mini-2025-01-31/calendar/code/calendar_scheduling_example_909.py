from z3 import Solver, Int, Or, sat

# Meeting parameters.
duration = 30  # meeting duration in minutes
WORK_START = 9 * 60    # 9:00 AM in minutes (540)
WORK_END   = 17 * 60   # 17:00 in minutes (1020)

# Days encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Busy intervals for Jeremy.
# Each busy interval is expressed as a tuple (start, end) in minutes from midnight.
jeremy_busy = {
    0: [(12 * 60, 12 * 60 + 30)],                           # Monday: 12:00-12:30
    1: [(11 * 60 + 30, 12 * 60), (15 * 60, 15 * 60 + 30)],   # Tuesday: 11:30-12:00, 15:00-15:30
    2: [(10 * 60 + 30, 11 * 60), (14 * 60, 14 * 60 + 30),
        (15 * 60, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)],   # Wednesday: 10:30-11:00, 14:00-14:30, 15:00-15:30, 16:00-16:30
    3: [(13 * 60 + 30, 14 * 60), (15 * 60, 15 * 60 + 30)],   # Thursday: 13:30-14:00, 15:00-15:30
    4: [(14 * 60 + 30, 15 * 60)]                            # Friday: 14:30-15:00
}

# Busy intervals for Anna.
anna_busy = {
    0: [(9 * 60, 17 * 60)],                     # Monday: 9:00-17:00
    1: [(9 * 60, 17 * 60)],                     # Tuesday: 9:00-17:00
    2: [(9 * 60, 14 * 60), (14 * 60 + 30, 17 * 60)],  # Wednesday: 9:00-14:00, 14:30-17:00
    3: [(9 * 60, 11 * 60 + 30), (12 * 60 + 30, 15 * 60), (16 * 60 + 30, 17 * 60)],  # Thursday: 9:00-11:30, 12:30-15:00, 16:30-17:00
    4: [(9 * 60, 13 * 60 + 30), (14 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)]  # Friday: 9:00-13:30, 14:00-16:00, 16:30-17:00
}

# Additional preferences:
# Jeremy would like to avoid meetings on Thursday after 13:00 and to avoid Friday.
# So, our primary candidate day will be Thursday (day 3) subject to the meeting starting before 13:00,
# and we will use Friday (day 4) as a backup option if necessary.
primary_days = [3]
backup_days = [4]

def no_overlap(busy_start, busy_end, s, duration):
    # This function ensures that the meeting (from time s to s+duration)
    # does not overlap with a busy interval [busy_start, busy_end).
    return Or(s + duration <= busy_start, s >= busy_end)

def find_earliest_meeting_time(candidate_days):
    # Try each candidate day in order.
    for day in candidate_days:
        solver = Solver()
        # Meeting start time variable in minutes.
        s = Int("s")
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Enforce additional preference for Thursday: meeting must start before 13:00.
        if day == 3:
            solver.add(s < 13 * 60)

        # Add Jeremy's busy intervals constraints if any for the candidate day.
        if day in jeremy_busy:
            for start_busy, end_busy in jeremy_busy[day]:
                solver.add(no_overlap(start_busy, end_busy, s, duration))
                
        # Add Anna's busy intervals constraints if any for the candidate day.
        if day in anna_busy:
            for start_busy, end_busy in anna_busy[day]:
                solver.add(no_overlap(start_busy, end_busy, s, duration))
                
        # Since we want the earliest availability, iterate through start times in ascending order.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

# First, try the primary days.
day, t = find_earliest_meeting_time(primary_days)

# If no valid meeting time is found in the primary candidate, try the backup days (Friday).
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