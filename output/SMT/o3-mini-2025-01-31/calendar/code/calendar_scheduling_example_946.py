from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
WORK_START = 9 * 60    # 9:00 in minutes (540)
WORK_END = 17 * 60     # 17:00 in minutes (1020)

# Day encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Juan's busy intervals (in minutes)
# Monday: 11:00 to 11:30
# Tuesday: 11:30 to 12:00, 12:30 to 13:30, 15:30 to 16:00
# Wednesday: 14:30 to 15:00
# Thursday: 15:30 to 16:00
# Friday: 10:30 to 11:00
juan_busy = {
    0: [(11*60, 11*60+30)],
    1: [(11*60+30, 12*60), (12*60+30, 13*60+30), (15*60+30, 16*60)],
    2: [(14*60+30, 15*60)],
    3: [(15*60+30, 16*60)],
    4: [(10*60+30, 11*60)]
}

# Doris's busy intervals (in minutes)
# Monday: 9:00 to 17:00 (completely busy)
# Tuesday: 9:00 to 15:30, 16:00 to 16:30
# Wednesday: 9:00 to 9:30, 10:00 to 12:30, 14:00 to 14:30, 15:00 to 16:00, 16:30 to 17:00
# Thursday: 9:30 to 13:00, 14:00 to 15:30, 16:00 to 17:00
# Friday: 9:00 to 10:00, 10:30 to 12:00, 13:00 to 14:30, 15:00 to 17:00
doris_busy = {
    0: [(9*60, 17*60)],
    1: [(9*60, 15*60+30), (16*60, 16*60+30)],
    2: [(9*60, 9*60+30), (10*60, 12*60+30), (14*60, 14*60+30), (15*60, 16*60), (16*60+30, 17*60)],
    3: [(9*60+30, 13*60), (14*60, 15*60+30), (16*60, 17*60)],
    4: [(9*60, 10*60), (10*60+30, 12*60), (13*60, 14*60+30), (15*60, 17*60)]
}

# Doris would like to avoid Tuesday and Friday. To represent this preference,
# we will first try to find a time on days without these undesirable days.
# That is, we will prioritize Wednesday (2) and Thursday (3), then try Tuesday (1) and Friday (4).
preferred_days_order = [2, 3, 1, 4]

def no_overlap(busy_start, busy_end, meeting_start, duration):
    # The meeting interval [meeting_start, meeting_start+duration)
    # must not overlap with a busy interval [busy_start, busy_end)
    return Or(meeting_start + duration <= busy_start, meeting_start >= busy_end)

def find_earliest_meeting():
    for day in preferred_days_order:
        solver = Solver()
        s = Int("s")  # meeting start time (minutes since midnight)

        # Meeting must fit within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add Juan's busy constraints for the day.
        if day in juan_busy:
            for (busy_start, busy_end) in juan_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))

        # Add Doris's busy constraints for the day.
        if day in doris_busy:
            for (busy_start, busy_end) in doris_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))

        # Try each minute in the workday in order to find the earliest valid meeting start time.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()

    return None, None

day, start_time = find_earliest_meeting()

if day is not None and start_time is not None:
    meeting_end = start_time + duration
    start_hour, start_minute = divmod(start_time, 60)
    end_hour, end_minute = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
        day_names[day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time found that satisfies all constraints.")