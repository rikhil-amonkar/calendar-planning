from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60                # meeting duration: 60 minutes (1 hour)
WORK_START = 9 * 60          # 9:00 -> 540 minutes
WORK_END = 17 * 60           # 17:00 -> 1020 minutes

# Day mapping: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0:"Monday", 1:"Tuesday", 2:"Wednesday", 3:"Thursday", 4:"Friday"}

# Lisa's busy intervals (in minutes)
# Monday: 10:30-11:30, 12:00-12:30, 13:30-14:00, 16:30-17:00
# Tuesday: 10:30-11:00, 13:30-14:00, 16:30-17:00
# Thursday: 12:00-12:30
# Friday: 9:00-9:30
lisa_busy = {
    0: [(10 * 60 + 30, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), (13 * 60 + 30, 14 * 60), (16 * 60 + 30, 17 * 60)],
    1: [(10 * 60 + 30, 11 * 60), (13 * 60 + 30, 14 * 60), (16 * 60 + 30, 17 * 60)],
    3: [(12 * 60, 12 * 60 + 30)],
    4: [(9 * 60, 9 * 60 + 30)]
}

# Emily's busy intervals (in minutes)
# Monday: 9:30-10:00, 10:30-11:30, 12:00-15:00, 16:30-17:00
# Tuesday: 9:00-15:00, 15:30-17:00
# Wednesday: 9:00-10:30, 12:00-13:30, 14:00-15:00, 15:30-16:00
# Thursday: 9:30-10:00, 10:30-11:30, 14:30-15:30, 16:00-17:00
# Friday: 9:00-16:00, 16:30-17:00
emily_busy = {
    0: [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60 + 30), (12 * 60, 15 * 60), (16 * 60 + 30, 17 * 60)],
    1: [(9 * 60, 15 * 60), (15 * 60 + 30, 17 * 60)],
    2: [(9 * 60, 10 * 60 + 30), (12 * 60, 13 * 60 + 30), (14 * 60, 15 * 60), (15 * 60 + 30, 16 * 60)],
    3: [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60 + 30), (14 * 60 + 30, 15 * 60 + 30), (16 * 60, 17 * 60)],
    4: [(9 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)]
}

# Avoid constraints:
# Lisa cannot meet on Monday and Wednesday, so skip days 0 and 2.
lisa_avoid = {0, 2}

def no_overlap(busy_start, busy_end, s, dur):
    # Meeting interval [s, s+dur) does not overlap with busy interval [busy_start, busy_end)
    return Or(s + dur <= busy_start, s >= busy_end)

def find_earliest_meeting():
    # Check days in order: Monday (0) -> Friday (4)
    for day in range(5):
        # Skip days that Lisa avoids.
        if day in lisa_avoid:
            continue

        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight

        # Meeting must fit within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add Lisa's busy intervals if any are scheduled on that day.
        if day in lisa_busy:
            for busy_start, busy_end in lisa_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Add Emily's busy intervals for this day.
        if day in emily_busy:
            for busy_start, busy_end in emily_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))

        # Try possible start times (earliest first)
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                model = solver.model()
                return day, model[s].as_long()
            solver.pop()
    return None, None

day, start_time = find_earliest_meeting()

if day is not None and start_time is not None:
    meeting_end = start_time + duration
    sh, sm = divmod(start_time, 60)
    eh, em = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
          day_names[day], sh, sm, eh, em))
else:
    print("No valid meeting time found that satisfies all constraints.")