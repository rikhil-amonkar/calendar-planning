from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30                  # meeting length in minutes
WORK_START = 9 * 60            # 9:00 AM in minutes (540)
WORK_END = 17 * 60             # 5:00 PM in minutes (1020)

# Mapping days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0:"Monday", 1:"Tuesday", 2:"Wednesday", 3:"Thursday", 4:"Friday"}

# Rachel's busy intervals (times in minutes)
rachel_busy = {
    0: [(540, 720), (780, 870), (900, 930), (960, 990)],  # Monday: 9-12, 13-14:30, 15-15:30, 16-16:30
    1: [(600, 660), (720, 750), (780, 810), (870, 930), (960, 990)],  # Tuesday: 10-11, 12-12:30, 13-13:30, 14:30-15:30, 16-16:30
    2: [(570, 630), (780, 900)],                           # Wednesday: 9:30-10:30, 13-15
    3: [(540, 570), (750, 810), (840, 900), (990, 1020)],   # Thursday: 9-9:30, 12:30-13:30, 14-15, 16:30-17
    4: [(540, 570), (660, 780), (810, 870), (960, 990)]     # Friday: 9-9:30, 11-13, 13:30-14:30, 16-16:30
}

# Brandon's busy intervals (times in minutes)
brandon_busy = {
    0: [(540, 570), (600, 660), (690, 840), (930, 1020)],  # Monday: 9-9:30, 10-11, 11:30-14, 15:30-17
    1: [(540, 600), (630, 1020)],                           # Tuesday: 9-10, 10:30-17
    2: [(540, 900), (930, 1020)],                           # Wednesday: 9-15, 15:30-17
    3: [(540, 660), (690, 810), (840, 1020)],               # Thursday: 9-11, 11:30-13:30, 14-17
    4: [(540, 930), (960, 1020)]                            # Friday: 9-15:30, 16-17
}

# Day avoid preferences:
# Rachel does NOT want to meet on Friday (day 4)
# Brandon would rather not meet on Thursday (day 3)
rachel_avoid = {4}
brandon_avoid = {3}

def no_overlap(busy_start, busy_end, s, dur):
    # Returns a constraint: meeting [s, s+dur) does not overlap with [busy_start, busy_end)
    return Or(s + dur <= busy_start, s >= busy_end)

def find_earliest_meeting():
    # Check days in order Monday (0) -> Friday (4)
    for day in range(5):
        # Skip day if either participant wants to avoid it
        if day in rachel_avoid or day in brandon_avoid:
            continue

        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight

        # Ensure meeting is within work hours
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add Rachel busy constraints for this day, if any.
        if day in rachel_busy:
            for (busy_start, busy_end) in rachel_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))

        # Add Brandon busy constraints for this day, if any.
        if day in brandon_busy:
            for (busy_start, busy_end) in brandon_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))

        # Check each minute in the range WORK_START...WORK_END - duration for a valid start time.
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