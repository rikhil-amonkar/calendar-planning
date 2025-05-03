from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
WORK_START = 9 * 60    # 9:00 AM in minutes (540)
WORK_END = 17 * 60     # 17:00 in minutes (1020)

# Days of the week: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Define each participant's busy intervals (times in minutes from midnight)
# Joseph's busy intervals:
#   Tuesday: 9:00 to 9:30, Thursday: 9:30 to 10:00.
joseph_busy = {
    1: [(9*60, 9*60+30)],        # Tuesday
    3: [(9*60+30, 10*60)]        # Thursday
}

# Gary's busy intervals:
#   Monday: 9:00-9:30, 10:00-10:30, 11:00-15:00, 15:30-17:00
#   Tuesday: 9:00-13:00, 13:30-14:30, 15:30-17:00
#   Wednesday: 9:00-9:30, 10:00-13:00, 13:30-17:00
#   Thursday: 9:00-9:30, 10:30-13:00, 13:30-17:00
#   Friday: 9:00-14:30, 15:00-17:00
gary_busy = {
    0: [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 15*60), (15*60+30, 17*60)],
    1: [(9*60, 13*60), (13*60+30, 14*60+30), (15*60+30, 17*60)],
    2: [(9*60, 9*60+30), (10*60, 13*60), (13*60+30, 17*60)],
    3: [(9*60, 9*60+30), (10*60+30, 13*60), (13*60+30, 17*60)],
    4: [(9*60, 14*60+30), (15*60, 17*60)]
}

# Preferences: "would rather not" means we avoid these days.
# Joseph would rather not meet on Monday (0), Tuesday (1), or Thursday (3).
# Gary does not want to meet on Wednesday (2).
joseph_pref_unwanted = {0, 1, 3}
gary_pref_unwanted = {2}

def no_overlap(busy_start, busy_end, meeting_start, duration):
    # Meeting interval is [meeting_start, meeting_start+duration)
    # Busy interval is [busy_start, busy_end)
    # They do not overlap if the meeting finishes before busy_start
    # or starts at or after busy_end.
    return Or(meeting_start + duration <= busy_start, meeting_start >= busy_end)

def find_meeting_time():
    # We explore each day Monday(0) to Friday(4)
    for day in range(5):
        # Check preferences: skip day if it is unwanted by any participant.
        if day in joseph_pref_unwanted:
            continue
        if day in gary_pref_unwanted:
            continue

        # Setup a fresh solver for the day
        solver = Solver()
        s = Int("s")  # meeting start time in minutes since midnight

        # Meeting must be within the work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add Joseph's busy constraints for the day (if any)
        if day in joseph_busy:
            for busy_start, busy_end in joseph_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))

        # Add Gary's busy constraints for the day (if any)
        if day in gary_busy:
            for busy_start, busy_end in gary_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))

        # Search over possible start times minute-by-minute, preferring the earliest.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

day, start_time = find_meeting_time()

if day is not None and start_time is not None:
    meeting_end = start_time + duration
    start_hour, start_minute = divmod(start_time, 60)
    end_hour, end_minute = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
        day_names[day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time found that satisfies all constraints.")