from z3 import Solver, Int, Or, sat

# Meeting parameters: 30 minutes duration, work hours 9:00 (540) to 17:00 (1020) minutes.
duration = 30
WORK_START = 9 * 60    # 540 minutes
WORK_END   = 17 * 60   # 1020 minutes

# Days encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Dorothy's busy intervals.
# Each interval is given as (start, end) in minutes.
dorothy_busy = {
    0: [(12*60, 12*60+30),    # Monday: 12:00-12:30
        (13*60+30, 14*60),    # Monday: 13:30-14:00
        (15*60+30, 16*60),    # Monday: 15:30-16:00
        (16*60+30, 17*60)],   # Monday: 16:30-17:00
    1: [(9*60+30, 10*60+30),  # Tuesday: 9:30-10:30
        (11*60, 11*60+30),    # Tuesday: 11:00-11:30
        (13*60, 13*60+30)],   # Tuesday: 13:00-13:30
    2: [(9*60+30, 10*60+30),  # Wednesday: 9:30-10:30
        (11*60, 12*60),       # Wednesday: 11:00-12:00
        (13*60, 14*60),       # Wednesday: 13:00-14:00
        (16*60+30, 17*60)],   # Wednesday: 16:30-17:00
    3: [(9*60, 9*60+30),     # Thursday: 9:00-9:30
        (14*60, 14*60+30),   # Thursday: 14:00-14:30
        (15*60, 15*60+30)],   # Thursday: 15:00-15:30
    4: [(10*60+30, 11*60),       # Friday: 10:30-11:00
        (11*60+30, 12*60),       # Friday: 11:30-12:00
        (12*60+30, 13*60),       # Friday: 12:30-13:00
        (13*60+30, 14*60+30),    # Friday: 13:30-14:30
        (15*60, 15*60+30)]       # Friday: 15:00-15:30
}

# Lawrence's busy intervals.
# Note: On Monday through Thursday, Lawrence is busy the entire day.
lawrence_busy = {
    0: [(9*60, 17*60)],           # Monday: 9:00-17:00
    1: [(9*60, 17*60)],           # Tuesday: 9:00-17:00
    2: [(9*60, 17*60)],           # Wednesday: 9:00-17:00
    3: [(9*60, 17*60)],           # Thursday: 9:00-17*60
    4: [(9*60+30, 10*60+30),       # Friday: 9:30-10:30
        (11*60, 14*60),           # Friday: 11:00-14:00
        (14*60+30, 16*60),        # Friday: 14:30-16:00
        (16*60+30, 17*60)]        # Friday: 16:30-17:00
}

# Additional constraint for Lawrence: On Friday, he cannot meet before 11:30.
LAWRENCE_FRIDAY_MIN_START = 11*60 + 30  # 11:30 in minutes

def no_overlap(busy_start, busy_end, s, dur):
    # Returns constraint that the meeting (s to s+dur) does not overlap [busy_start, busy_end)
    return Or(s + dur <= busy_start, s >= busy_end)

def find_earliest_meeting(ordered_days):
    for day in ordered_days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        # If the meeting is on Friday, enforce Lawrence's additional constraint.
        if day == 4:
            solver.add(s >= LAWRENCE_FRIDAY_MIN_START)
        
        # Add Dorothy's busy constraints if any on the day.
        if day in dorothy_busy:
            for busy_start, busy_end in dorothy_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Add Lawrence's busy constraints if any on the day.
        if day in lawrence_busy:
            for busy_start, busy_end in lawrence_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Try each possible minute to find the earliest availability.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

# Order of days to search: Monday (0) to Friday (4)
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