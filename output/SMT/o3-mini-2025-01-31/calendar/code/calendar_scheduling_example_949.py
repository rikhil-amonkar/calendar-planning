from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
WORK_START = 9 * 60    # 9:00 AM in minutes (540)
WORK_END = 17 * 60     # 17:00 in minutes (1020)

# Days of the week: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Margaret's busy intervals (in minutes)
# Monday: 9:00-9:30, 10:30-11:30, 13:30-14:00, 14:30-15:30, 16:00-17:00
# Tuesday: 9:30-10:00, 12:00-12:30, 14:30-17:00
# Wednesday: 10:00-10:30, 11:00-11:30, 12:30-13:00, 15:00-15:30, 16:00-17:00
# Thursday: 9:30-10:00, 10:30-11:00, 11:30-12:00, 15:00-15:30, 16:30-17:00
# Friday: 9:00-9:30, 11:00-12:00, 13:30-14:00, 15:30-16:00, 16:30-17:00
margaret_busy = {
    0: [(9*60, 9*60+30), (10*60+30, 11*60+30), (13*60+30, 14*60), (14*60+30, 15*60+30), (16*60, 17*60)],
    1: [(9*60+30, 10*60), (12*60, 12*60+30), (14*60+30, 17*60)],
    2: [(10*60, 10*60+30), (11*60, 11*60+30), (12*60+30, 13*60), (15*60, 15*60+30), (16*60, 17*60)],
    3: [(9*60+30, 10*60), (10*60+30, 11*60), (11*60+30, 12*60), (15*60, 15*60+30), (16*60+30, 17*60)],
    4: [(9*60, 9*60+30), (11*60, 12*60), (13*60+30, 14*60), (15*60+30, 16*60), (16*60+30, 17*60)]
}

# Denise's busy intervals (in minutes)
# Monday: 9:30-12:00, 13:00-14:00, 15:00-16:00
# Tuesday: 9:00-17:00  (entire day busy)
# Wednesday: 9:00-11:00, 11:30-16:00
# Thursday: 9:00-14:00, 14:30-15:30, 16:30-17:00
# Friday: 9:00-11:00, 12:00-15:30
denise_busy = {
    0: [(9*60+30, 12*60), (13*60, 14*60), (15*60, 16*60)],
    1: [(9*60, 17*60)],  # Fully busy Tuesday.
    2: [(9*60, 11*60), (11*60+30, 16*60)],
    3: [(9*60, 14*60), (14*60+30, 15*60+30), (16*60+30, 17*60)],
    4: [(9*60, 11*60), (12*60, 15*60+30)]
}

def no_overlap(busy_start, busy_end, meeting_start, duration):
    # Ensures that the meeting interval [meeting_start, meeting_start+duration)
    # does not overlap with [busy_start, busy_end)
    return Or(meeting_start + duration <= busy_start, meeting_start >= busy_end)

def find_earliest_meeting():
    # We need to consider Monday to Friday, but note Denise cannot meet on Friday.
    # So we'll skip day 4 (Friday).
    for day in range(5):
        if day == 4:  # Denise cannot meet on Friday.
            continue

        solver = Solver()
        s = Int("s")  # meeting start time in minutes since midnight

        # Meeting must fall within the work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # For Margaret's additional preference: she would rather not meet on Monday after 13:30.
        # So if day is Monday (0), force the meeting to finish by 13:30 (i.e., s + duration <= 13:30)
        if day == 0:
            solver.add(s + duration <= 13*60 + 30)  # 13:30 in minutes is 810

        # Add Margaret's busy intervals for the chosen day.
        if day in margaret_busy:
            for busy_start, busy_end in margaret_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))

        # Add Denise's busy intervals for the chosen day.
        if day in denise_busy:
            for busy_start, busy_end in denise_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))

        # Check each minute in the working window for the earliest valid start time.
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