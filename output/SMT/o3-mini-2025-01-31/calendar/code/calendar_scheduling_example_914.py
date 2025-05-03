from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (1 hour)
WORK_START = 9 * 60   # 9:00 AM = 540 minutes
WORK_END = 17 * 60    # 17:00 = 1020 minutes

# Days encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Benjamin's busy intervals (times in minutes)
benjamin_busy = {
    0: [(11 * 60, 11 * 60 + 30),    # Monday: 11:00 - 11:30
        (16 * 60, 16 * 60 + 30)],   # Monday: 16:00 - 16:30
    1: [(13 * 60, 13 * 60 + 30)],    # Tuesday: 13:00 - 13:30
    2: [(11 * 60 + 30, 12 * 60),     # Wednesday: 11:30 - 12:00
        (13 * 60, 14 * 60),          # Wednesday: 13:00 - 14:00
        (16 * 60 + 30, 17 * 60)],     # Wednesday: 16:30 - 17:00
    3: [(9 * 60, 9 * 60 + 30),       # Thursday: 9:00 - 9:30
        (15 * 60, 15 * 60 + 30)],     # Thursday: 15:00 - 15:30
    4: [(12 * 60 + 30, 13 * 60),     # Friday: 12:30 - 13:00
        (13 * 60 + 30, 14 * 60),     # Friday: 13:30 - 14:00
        (16 * 60, 16 * 60 + 30)]      # Friday: 16:00 - 16:30
}

# Melissa's busy intervals (times in minutes)
melissa_busy = {
    0: [(9 * 60, 16 * 60),         # Monday: 9:00 - 16:00
        (16 * 60 + 30, 17 * 60)],   # Monday: 16:30 - 17:00
    1: [(9 * 60, 9 * 60 + 30),      # Tuesday: 9:00 - 9:30
        (10 * 60, 11 * 60),         # Tuesday: 10:00 - 11:00
        (12 * 60, 12 * 60 + 30),    # Tuesday: 12:00 - 12:30
        (13 * 60, 13 * 60 + 30),    # Tuesday: 13:00 - 13:30
        (14 * 60, 17 * 60)],        # Tuesday: 14:00 - 17:00
    2: [(9 * 60, 10 * 60),         # Wednesday: 9:00 - 10:00
        (12 * 60, 12 * 60 + 30),    # Wednesday: 12:00 - 12:30
        (13 * 60, 13 * 60 + 30),    # Wednesday: 13:00 - 13:30
        (14 * 60, 15 * 60),         # Wednesday: 14:00 - 15:00
        (15 * 60 + 30, 16 * 60),    # Wednesday: 15:30 - 16:00
        (16 * 60 + 30, 17 * 60)],   # Wednesday: 16:30 - 17:00
    3: [(9 * 60, 10 * 60 + 30),    # Thursday: 9:00 - 10:30
        (11 * 60, 15 * 60),         # Thursday: 11:00 - 15:00
        (15 * 60 + 30, 16 * 60 + 30)],# Thursday: 15:30 - 16:30
    4: [(9 * 60, 12 * 60),         # Friday: 9:00 - 12:00
        (12 * 60 + 30, 17 * 60)]    # Friday: 12:30 - 17:00
}

# Helper function that returns a constraint ensuring that the meeting
# defined by start time s and duration does not overlap with a busy interval.
def no_overlap(busy_start, busy_end, s, duration):
    # Either the meeting ends before busy_start or starts after busy_end.
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find the earliest meeting time for a given ordered list of days.
def find_earliest_meeting(ordered_days):
    for day in ordered_days:
        solver = Solver()
        s = Int("s")  # meeting start time (in minutes from midnight)
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Benjamin's busy constraints for this day.
        if day in benjamin_busy:
            for busy_start, busy_end in benjamin_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Add Melissa's busy constraints for this day.
        if day in melissa_busy:
            for busy_start, busy_end in melissa_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Try to assign the earliest possible start minute.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    
    return None, None

# Days ordered from Monday to Friday
ordered_days = [0, 1, 2, 3, 4]
day, t = find_earliest_meeting(ordered_days)

if day is not None and t is not None:
    meeting_end = t + duration
    start_hr, start_min = divmod(t, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
        day_names[day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")