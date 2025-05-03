from z3 import Solver, Int, Or, sat

# Meeting parameters: 30 minutes meeting, work hours 9:00 (540) to 17:00 (1020) minutes.
duration = 30
WORK_START = 9 * 60    # 540 minutes
WORK_END   = 17 * 60   # 1020 minutes

# Days encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Brittany's busy intervals.
# Note: Only intervals given for Wednesday and Friday.
brittany_busy = {
    2: [(9*60 + 30, 10*60 + 30),  # Wednesday: 9:30-10:30
        (11*60, 11*60 + 30),      # Wednesday: 11:00-11:30
        (13*60 + 30, 14*60),      # Wednesday: 13:30-14:00
        (15*60, 15*60 + 30)],     # Wednesday: 15:00-15:30
    4: [(9*60, 9*60 + 30)]         # Friday: 9:00-9:30
}

# Judith's busy intervals.
judith_busy = {
    0: [(9*60, 10*60),          # Monday: 9:00-10:00
        (10*60 + 30, 13*60),     # Monday: 10:30-13:00
        (13*60 + 30, 15*60),     # Monday: 13:30-15:00
        (16*60, 17*60)],        # Monday: 16:00-17:00
    1: [(9*60, 10*60),          # Tuesday: 9:00-10:00
        (11*60, 11*60 + 30),     # Tuesday: 11:00-11:30
        (12*60, 13*60 + 30),     # Tuesday: 12:00-13:30
        (14*60, 15*60 + 30)],    # Tuesday: 14:00-15:30
    2: [(9*60, 17*60)],         # Wednesday: 9:00-17:00 (completely busy)
    3: [(9*60, 9*60 + 30),       # Thursday: 9:00-9:30
        (10*60, 14*60),         # Thursday: 10:00-14:00
        (14*60 + 30, 17*60)],    # Thursday: 14:30-17:00
    4: [(9*60, 11*60),          # Friday: 9:00-11:00
        (12*60, 12*60 + 30),     # Friday: 12:00-12:30
        (14*60 + 30, 15*60),     # Friday: 14:30-15:00
        (16*60 + 30, 17*60)]     # Friday: 16:30-17:00
}

# The group wants to meet at their earliest availability across Monday-Friday.
# We'll simply try days in order (0 to 4) and find the earliest minute for which
# both participants have a free slot of the specified duration.

def no_overlap(busy_start, busy_end, s, dur):
    # Meeting from s to s+dur must not overlap busy interval [busy_start, busy_end).
    return Or(s + dur <= busy_start, s >= busy_end)

def find_earliest_meeting(ordered_days):
    for day in ordered_days:
        solver = Solver()
        s = Int("s")  # meeting start time as minutes from midnight
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add Brittany's busy constraints if she has meetings on this day.
        if day in brittany_busy:
            for b_start, b_end in brittany_busy[day]:
                solver.add(no_overlap(b_start, b_end, s, duration))
        
        # Add Judith's busy constraints if she has meetings on this day.
        if day in judith_busy:
            for j_start, j_end in judith_busy[day]:
                solver.add(no_overlap(j_start, j_end, s, duration))

        # Try each possible start time in incremental order to get earliest availability.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

# Define the order of days to search: Monday (0), Tuesday (1), Wednesday (2), Thursday (3), Friday (4)
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