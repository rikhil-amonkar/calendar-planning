from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60                # meeting length: 60 minutes (1 hour)
WORK_START = 9 * 60          # 9:00 AM in minutes (540)
WORK_END = 17 * 60           # 5:00 PM in minutes (1020)

# Days: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Betty's busy intervals (in minutes)
# Monday: 10:00-10:30, 11:30-12:30, 16:00-16:30
# Tuesday: 9:30-10:00, 10:30-11:00, 12:00-12:30, 13:30-15:00, 16:30-17:00
# Wednesday: 13:30-14:00, 14:30-15:00
# Friday: 9:00-10:00, 11:30-12:00, 12:30-13:00, 14:30-15:00
betty_busy = {
    0: [(10 * 60, 10 * 60 + 30), (11 * 60 + 30, 12 * 60 + 30), (16 * 60, 16 * 60 + 30)],
    1: [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60), (12 * 60, 12 * 60 + 30), (13 * 60 + 30, 15 * 60), (16 * 60 + 30, 17 * 60)],
    2: [(13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60)],
    4: [(9 * 60, 10 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60), (14 * 60 + 30, 15 * 60)]
}

# Megan's busy intervals (in minutes)
# Monday: 9:00-17:00
# Tuesday: 9:00-9:30, 10:00-10:30, 12:00-14:00, 15:00-15:30, 16:00-16:30
# Wednesday: 9:30-10:30, 11:00-11:30, 12:30-13:00, 13:30-14:30, 15:30-17:00
# Thursday: 9:00-10:30, 11:30-14:00, 14:30-15:00, 15:30-16:30
# Friday: 9:00-17:00
megan_busy = {
    0: [(9 * 60, 17 * 60)],
    1: [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (12 * 60, 14 * 60), (15 * 60, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)],
    2: [(9 * 60 + 30, 10 * 60 + 30), (11 * 60, 11 * 60 + 30), (12 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60 + 30), (15 * 60 + 30, 17 * 60)],
    3: [(9 * 60, 10 * 60 + 30), (11 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60 + 30)],
    4: [(9 * 60, 17 * 60)]
}

# Betty's avoid days: Betty cannot meet on Wednesday (2) or Thursday (3)
betty_avoid = {2, 3}

def no_overlap(busy_start, busy_end, s, dur):
    # The meeting [s, s+dur) should not overlap with a busy interval [busy_start, busy_end)
    return Or(s + dur <= busy_start, s >= busy_end)

def find_earliest_meeting():
    # Iterate over days Monday to Friday
    for day in range(5):
        # Skip if Betty avoids the day
        if day in betty_avoid:
            continue

        solver = Solver()
        s = Int("s")  # meeting start time (in minutes from midnight)

        # Ensure the meeting is during working hours
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Constrain against Betty's busy intervals (if any) for this day
        if day in betty_busy:
            for busy_start, busy_end in betty_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Constrain against Megan's busy intervals (if any) for this day
        if day in megan_busy:
            for busy_start, busy_end in megan_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Try possible start times in increasing order (earliest first)
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