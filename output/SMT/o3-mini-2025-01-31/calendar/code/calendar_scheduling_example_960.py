from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30                  # meeting duration in minutes
WORK_START = 9 * 60            # work day starts at 9:00 -> 540 minutes
WORK_END = 17 * 60             # work day ends at 17:00 -> 1020 minutes

# Mapping for day names: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {
    0: "Monday",
    1: "Tuesday",
    2: "Wednesday",
    3: "Thursday",
    4: "Friday"
}

# Adam's busy intervals (in minutes):
# Tuesday:    9:30 to 10:00 -> (570, 600)
# Wednesday:  14:00 to 14:30 -> (840, 870)
# Thursday:   13:00 to 13:30 -> (780, 810)
# Friday:     15:00 to 15:30 -> (900, 930)
adam_busy = {
    1: [(9 * 60 + 30, 10 * 60)],
    2: [(14 * 60, 14 * 60 + 30)],
    3: [(13 * 60, 13 * 60 + 30)],
    4: [(15 * 60, 15 * 60 + 30)]
}

# Karen's busy intervals (in minutes):
# Monday:    9:30-10:00 -> (570,600); 12:00-12:30 -> (720,750);
#            13:30-14:00 -> (810,840); 15:00-15:30 -> (900,930);
#            16:00-17:00 -> (960,1020)
# Tuesday:   10:00-11:30 -> (600,690); 12:00-12:30 -> (720,750);
#            13:30-14:30 -> (810,870); 15:30-16:00 -> (930,960);
#            16:30-17:00 -> (990,1020)
# Wednesday: 9:00-9:30   -> (540,570); 10:30-14:00 -> (630,840);
#            14:30-17:00  -> (870,1020)
# Thursday:  9:00-9:30   -> (540,570); 10:00-10:30 -> (600,630);
#            11:00-11:30  -> (660,690); 12:00-13:30 -> (720,810);
#            15:00-15:30  -> (900,930); 16:00-16:30 -> (960,990)
# Friday:    9:30-10:00  -> (570,600); 11:30-12:30 -> (690,750);
#            13:00-16:00  -> (780,960)
karen_busy = {
    0: [(9 * 60 + 30, 10 * 60), (12 * 60, 12 * 60 + 30), (13 * 60 + 30, 14 * 60), (15 * 60, 15 * 60 + 30), (16 * 60, 17 * 60)],
    1: [(10 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), (13 * 60 + 30, 14 * 60 + 30), (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)],
    2: [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 14 * 60), (14 * 60 + 30, 17 * 60)],
    3: [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (11 * 60, 11 * 60 + 30), (12 * 60, 13 * 60 + 30), (15 * 60, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)],
    4: [(9 * 60 + 30, 10 * 60), (11 * 60 + 30, 12 * 60 + 30), (13 * 60, 16 * 60)]
}

# Avoid constraints:
# Adam would like to avoid meetings on Monday (day 0)
# Karen would like to avoid meetings on Wednesday (day 2)
adam_avoid = {0}
karen_avoid = {2}

def no_overlap(busy_start, busy_end, s, dur):
    # Constraint: meeting [s, s+dur) does not overlap with [busy_start, busy_end)
    return Or(s + dur <= busy_start, s >= busy_end)

def find_earliest_meeting():
    # Iterate over each day Monday (0) to Friday (4); we search in order for the earliest available opportunity
    for day in range(5):
        if day in adam_avoid or day in karen_avoid:
            continue  # skip days that are to be avoided by any participant

        solver = Solver()
        s = Int("s")  # meeting start time (in minutes from midnight)

        # Meeting must be within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add Adam's busy constraints if any on this day.
        if day in adam_busy:
            for busy_start, busy_end in adam_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))

        # Add Karen's busy constraints if any on this day.
        if day in karen_busy:
            for busy_start, busy_end in karen_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))

        # Check each possible starting minute in the day, from WORK_START to WORK_END-duration.
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
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(day_names[day], sh, sm, eh, em))
else:
    print("No valid meeting time found that satisfies all constraints.")