from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30                    # meeting duration in minutes
WORK_START = 9 * 60              # work day starts at 9:00 (in minutes)
WORK_END = 17 * 60               # work day ends at 17:00 (in minutes)

# Days mapping: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Amber's busy intervals (times in minutes)
amber_busy = {
    0: [(13*60, 13*60+30), (15*60, 16*60), (16*60+30, 17*60)],  # Monday
    1: [(10*60+30, 12*60), (13*60, 14*60), (14*60+30, 15*60), (15*60+30, 16*60)],  # Tuesday
    2: [(9*60, 9*60+30), (11*60, 12*60), (13*60, 13*60+30), (14*60, 14*60+30), (15*60, 16*60)],  # Wednesday
    3: [(9*60, 11*60), (12*60, 14*60), (14*60+30, 16*60+30)],  # Thursday
    4: [(9*60+30, 10*60), (11*60, 12*60), (12*60+30, 13*60), (14*60, 14*60+30), (15*60+30, 16*60)]  # Friday
}

# Marie's busy intervals (times in minutes)
marie_busy = {
    0: [(9*60+30, 10*60+30), (12*60, 12*60+30), (14*60+30, 15*60+30), (16*60+30, 17*60)],  # Monday
    1: [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 13*60+30), (14*60+30, 16*60), (16*60+30, 17*60)],  # Tuesday
    2: [(9*60+30, 10*60+30), (11*60+30, 15*60)],  # Wednesday
    3: [(9*60, 10*60), (12*60+30, 13*60), (14*60, 14*60+30), (16*60, 17*60)],  # Thursday
    4: [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 12*60+30), (13*60, 14*60), (14*60+30, 15*60+30), (16*60, 16*60+30)]  # Friday
}

# Avoid constraints:
# Amber cannot meet on Thursday and Friday
amber_avoid = {3, 4}
# Marie does not want to meet on Monday and Tuesday
marie_avoid = {0, 1}

# Function to ensure that the meeting interval [s, s+duration) does not overlap a busy interval [busy_start, busy_end)
def no_overlap(busy_start, busy_end, s, dur):
    return Or(s + dur <= busy_start, s >= busy_end)

def find_earliest_meeting():
    # Iterate through days Monday to Friday in order
    for day in range(5):
        # Skip days that a participant prefers to avoid
        if day in amber_avoid or day in marie_avoid:
            continue

        solver = Solver()
        s = Int("s")  # meeting start time in minutes after midnight

        # Ensure the meeting stays within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add Amber's busy intervals constraints for the day (if any)
        if day in amber_busy:
            for b_start, b_end in amber_busy[day]:
                solver.add(no_overlap(b_start, b_end, s, duration))

        # Add Marie's busy intervals constraints for the day (if any)
        if day in marie_busy:
            for b_start, b_end in marie_busy[day]:
                solver.add(no_overlap(b_start, b_end, s, duration))

        # Search minute by minute for the earliest valid start time.
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