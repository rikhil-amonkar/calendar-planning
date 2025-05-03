from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60                    # meeting duration in minutes (1 hour)
WORK_START = 9 * 60              # work day starts at 9:00 (in minutes: 540)
WORK_END = 17 * 60               # work day ends at 17:00 (in minutes: 1020)

# Days mapping: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Gerald's busy intervals (times in minutes)
# Monday:    12:00 to 12:30   -> (720, 750)
# Tuesday:   11:30 to 12:00   -> (690, 720)
# Thursday:  10:00 to 10:30   -> (600, 630)
# Friday:    11:00 to 11:30, 12:00 to 12:30, 14:00 to 14:30 -> (660,690), (720,750), (840,870)
gerald_busy = {
    0: [(12*60, 12*60+30)],
    1: [(11*60+30, 12*60)],
    3: [(10*60, 10*60+30)],
    4: [(11*60, 11*60+30), (12*60, 12*60+30), (14*60, 14*60+30)]
}

# Jeremy's busy intervals (times in minutes)
# Monday:    9:00 to 10:30, 11:30 to 12:30, 13:00 to 14:00, 14:30 to 17:00
# Tuesday:   9:00 to 10:30, 11:00 to 11:30, 12:00 to 12:30, 13:30 to 14:30, 15:30 to 17:00
# Wednesday: 9:00 to 11:30, 12:00 to 14:30, 15:00 to 16:00
# Thursday:  9:00 to 11:00, 11:30 to 13:00, 13:30 to 15:00, 15:30 to 17:00
# Friday:    9:30 to 12:00, 13:00 to 15:30, 16:00 to 16:30
jeremy_busy = {
    0: [(9*60, 10*60+30), (11*60+30, 12*60+30), (13*60, 14*60), (14*60+30, 17*60)],
    1: [(9*60, 10*60+30), (11*60, 11*60+30), (12*60, 12*60+30), (13*60+30, 14*60+30), (15*60+30, 17*60)],
    2: [(9*60, 11*60+30), (12*60, 14*60+30), (15*60, 16*60)],
    3: [(9*60, 11*60), (11*60+30, 13*60), (13*60+30, 15*60), (15*60+30, 17*60)],
    4: [(9*60+30, 12*60), (13*60, 15*60+30), (16*60, 16*60+30)]
}

# Avoid constraints:
# Gerald does not want to meet on Monday (0) and Tuesday (1)
gerald_avoid = {0, 1}
# Jeremy has no avoid-day constraints
jeremy_avoid = set()

# Function to ensure that the meeting interval [s, s+duration) does not overlap with a busy interval [busy_start, busy_end)
def no_overlap(busy_start, busy_end, s, dur):
    return Or(s + dur <= busy_start, s >= busy_end)

def find_earliest_meeting():
    # Iterate over days: Monday (0) to Friday (4)
    for day in range(5):
        # Skip days that a participant prefers to avoid.
        if day in gerald_avoid or day in jeremy_avoid:
            continue

        solver = Solver()
        s = Int("s")  # meeting start time (in minutes from midnight)
        
        # The meeting must occur within the work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Apply Gerald's busy constraints if any for the given day.
        if day in gerald_busy:
            for b_start, b_end in gerald_busy[day]:
                solver.add(no_overlap(b_start, b_end, s, duration))
        
        # Apply Jeremy's busy constraints if any for the given day.
        if day in jeremy_busy:
            for b_start, b_end in jeremy_busy[day]:
                solver.add(no_overlap(b_start, b_end, s, duration))
        
        # Iterate minute by minute to find the earliest valid start time.
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
    start_hour, start_minute = divmod(start_time, 60)
    end_hour, end_minute = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
        day_names[day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time found that satisfies all constraints.")