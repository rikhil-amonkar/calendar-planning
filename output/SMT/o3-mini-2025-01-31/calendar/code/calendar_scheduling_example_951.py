from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # 30 minutes meeting
WORK_START = 9 * 60    # 9:00 AM in minutes (540)
WORK_END = 17 * 60     # 17:00 in minutes (1020)

# Days of the week: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Nicholas' busy intervals (in minutes)
# Monday: 10:00 to 10:30, 12:30 to 13:00, 14:30 to 15:00, 15:30 to 16:00
# Tuesday: 10:00 to 10:30, 16:00 to 16:30
# Wednesday: 9:30 to 10:00, 14:00 to 15:00, 15:30 to 16:30
# Thursday: 11:00 to 11:30, 12:00 to 12:30, 13:30 to 14:00, 14:30 to 15:00, 16:00 to 16:30
# Friday: 11:30 to 12:00, 13:00 to 13:30, 15:00 to 15:30, 16:30 to 17:00
nicholas_busy = {
    0: [(10*60, 10*60+30), (12*60+30, 13*60), (14*60+30, 15*60), (15*60+30, 16*60)],
    1: [(10*60, 10*60+30), (16*60, 16*60+30)],
    2: [(9*60+30, 10*60), (14*60, 15*60), (15*60+30, 16*60+30)],
    3: [(11*60, 11*60+30), (12*60, 12*60+30), (13*60+30, 14*60), (14*60+30, 15*60), (16*60, 16*60+30)],
    4: [(11*60+30, 12*60), (13*60, 13*60+30), (15*60, 15*60+30), (16*60+30, 17*60)]
}

# Melissa's busy intervals (in minutes)
# Monday: 9:00 to 14:00, 14:30 to 15:30, 16:00 to 17:00
# Tuesday: 9:00 to 9:30, 10:00 to 10:30, 11:30 to 12:30, 13:00 to 14:00,
#          14:30 to 15:00, 16:00 to 17:00
# Wednesday: 9:30 to 10:00, 10:30 to 11:00, 12:00 to 13:00, 13:30 to 14:30, 15:30 to 16:30
# Thursday: 9:00 to 9:30, 10:00 to 13:00, 13:30 to 16:30
# Friday: 9:00 to 10:00, 10:30 to 16:30
melissa_busy = {
    0: [(9*60, 14*60), (14*60+30, 15*60+30), (16*60, 17*60)],
    1: [(9*60, 9*60+30), (10*60, 10*60+30), (11*60+30, 12*60+30),
        (13*60, 14*60), (14*60+30, 15*60), (16*60, 17*60)],
    2: [(9*60+30, 10*60), (10*60+30, 11*60), (12*60, 13*60),
        (13*60+30, 14*60+30), (15*60+30, 16*60+30)],
    3: [(9*60, 9*60+30), (10*60, 13*60), (13*60+30, 16*60+30)],
    4: [(9*60, 10*60), (10*60+30, 16*60+30)]
}

def no_overlap(busy_start, busy_end, meeting_start, duration):
    # Meeting interval: [meeting_start, meeting_start + duration)
    # Busy interval: [busy_start, busy_end)
    return Or(meeting_start + duration <= busy_start, meeting_start >= busy_end)

def find_earliest_meeting():
    # Iterate over the days Monday to Friday (0 to 4)
    for day in range(5):
        solver = Solver()
        s = Int("s")  # meeting start time in minutes since midnight
        # Meeting must be within the work hours:
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add Nicholas's busy intervals for the day:
        if day in nicholas_busy:
            for busy_start, busy_end in nicholas_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))

        # Add Melissa's busy intervals for the day:
        if day in melissa_busy:
            for busy_start, busy_end in melissa_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))

        # Try each minute in the work window, choosing the earliest available meeting
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