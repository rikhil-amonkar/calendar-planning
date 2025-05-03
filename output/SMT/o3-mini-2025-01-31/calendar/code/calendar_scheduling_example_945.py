from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
WORK_START = 9 * 60    # 9:00 in minutes (540)
WORK_END = 17 * 60     # 17:00 in minutes (1020)

# Day encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Patricia's busy intervals (in minutes)
# Monday: 9:00-10:30, 11:00-13:00, 14:00-14:30, 16:00-17:00
# Tuesday: 9:30-10:00, 12:30-13:00, 15:30-16:00
# Wednesday: 10:00-12:00, 12:30-13:00, 13:30-14:00, 15:00-16:00
# Thursday: 9:30-10:00, 10:30-11:00, 11:30-12:00, 12:30-13:00, 13:30-14:00, 14:30-16:30
# Friday: 11:00-11:30, 15:30-16:00
patricia_busy = {
    0: [(9*60, 10*60+30), (11*60, 13*60), (14*60, 14*60+30), (16*60, 17*60)],
    1: [(9*60+30, 10*60), (12*60+30, 13*60), (15*60+30, 16*60)],
    2: [(10*60, 12*60), (12*60+30, 13*60), (13*60+30, 14*60), (15*60, 16*60)],
    3: [(9*60+30, 10*60), (10*60+30, 11*60), (11*60+30, 12*60), (12*60+30, 13*60),
        (13*60+30, 14*60), (14*60+30, 16*60+30)],
    4: [(11*60, 11*60+30), (15*60+30, 16*60)]
}

# Sharon's busy intervals (in minutes)
# Monday: 9:00-9:30, 10:00-10:30, 11:00-15:30, 16:00-16:30
# Tuesday: 9:00-9:30, 10:00-13:30, 14:00-15:30, 16:00-17:00
# Wednesday: 9:00-15:30, 16:00-17:00
# Thursday: 9:00-10:30, 11:00-16:30
# Friday: 9:00-17:00
sharon_busy = {
    0: [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 15*60+30), (16*60, 16*60+30)],
    1: [(9*60, 9*60+30), (10*60, 13*60+30), (14*60, 15*60+30), (16*60, 17*60)],
    2: [(9*60, 15*60+30), (16*60, 17*60)],
    3: [(9*60, 10*60+30), (11*60, 16*60+30)],
    4: [(9*60, 17*60)]
}

# Patricia cannot meet on Tuesday.
allowed_days_for_patricia = {0, 2, 3, 4}

def no_overlap(busy_start, busy_end, meeting_start, duration):
    # Ensures that the meeting interval [meeting_start, meeting_start+duration)
    # does not overlap with a busy interval [busy_start, busy_end)
    return Or(meeting_start + duration <= busy_start, meeting_start >= busy_end)

def find_earliest_meeting():
    # Check days in order Monday (0), Tuesday (1), Wednesday (2), Thursday (3), Friday (4)
    for day in range(5):
        if day not in allowed_days_for_patricia:
            continue

        solver = Solver()
        s = Int("s")  # meeting start time (in minutes since midnight)

        # Ensure meeting fits in work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add Patricia's busy constraints for the day.
        if day in patricia_busy:
            for (busy_start, busy_end) in patricia_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))

        # Add Sharon's busy constraints for the day.
        if day in sharon_busy:
            for (busy_start, busy_end) in sharon_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))

        # Search for the earliest minute that yields a valid meeting time.
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