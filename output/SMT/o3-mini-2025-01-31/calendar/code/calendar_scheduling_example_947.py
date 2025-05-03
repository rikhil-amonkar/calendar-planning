from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (1 hour)
WORK_START = 9 * 60    # 9:00 AM -> 540 minutes
WORK_END = 17 * 60     # 5:00 PM -> 1020 minutes

# Days: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Teresa's busy intervals (in minutes)
# Monday: 10:00-10:30, 12:30-13:00, 13:30-14:00
# Tuesday: 15:00-16:00
# Wednesday: 11:30-12:30, 15:30-16:00
# Thursday: 10:30-11:30
# Friday: 10:30-11:00, 12:30-13:00
teresa_busy = {
    0: [(10*60, 10*60+30), (12*60+30, 13*60), (13*60+30, 14*60)],
    1: [(15*60, 16*60)],
    2: [(11*60+30, 12*60+30), (15*60+30, 16*60)],
    3: [(10*60+30, 11*60+30)],
    4: [(10*60+30, 11*60), (12*60+30, 13*60)]
}

# Keith's busy intervals (in minutes)
# Monday: 9:00-9:30, 10:00-10:30, 11:00-14:30, 16:00-16:30
# Tuesday: 9:30-13:00, 13:30-17:00
# Wednesday: 9:30-11:00, 11:30-14:30, 15:00-17:00
# Thursday: 9:00-12:00, 12:30-13:00, 13:30-16:30
# Friday: 9:00-17:00
keith_busy = {
    0: [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 14*60+30), (16*60, 16*60+30)],
    1: [(9*60+30, 13*60), (13*60+30, 17*60)],
    2: [(9*60+30, 11*60), (11*60+30, 14*60+30), (15*60, 17*60)],
    3: [(9*60, 12*60), (12*60+30, 13*60), (13*60+30, 16*60+30)],
    4: [(9*60, 17*60)]
}

def no_overlap(busy_start, busy_end, meeting_start, duration):
    """
    Returns a constraint ensuring that the meeting interval
    [meeting_start, meeting_start+duration) does not overlap with
    a busy interval [busy_start, busy_end).
    """
    return Or(meeting_start + duration <= busy_start, meeting_start >= busy_end)

def find_earliest_meeting():
    # Try days in order: Monday (0), Tuesday (1), Wednesday (2),
    # Thursday (3), and Friday (4)
    for day in range(5):
        solver = Solver()
        s = Int("s")  # meeting start time (in minutes since midnight)

        # Meeting must be within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add Teresa's busy constraints for the day.
        if day in teresa_busy:
            for (busy_start, busy_end) in teresa_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Add Keith's busy constraints for the day.
        if day in keith_busy:
            for (busy_start, busy_end) in keith_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Check each minute in the working window to find the earliest valid start time.
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