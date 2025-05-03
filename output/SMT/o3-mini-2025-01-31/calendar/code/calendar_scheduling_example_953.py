from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # 30 minutes meeting
WORK_START = 9 * 60    # 9:00 AM in minutes (540)
WORK_END = 17 * 60     # 17:00 in minutes (1020)

# Days mapping: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Linda's busy intervals by day (times in minutes from midnight)
# Monday: 9:00-9:30, 10:00-10:30, 11:00-11:30, 12:00-13:00, 13:30-14:00, 15:00-15:30, 16:00-17:00
# Tuesday: 9:00-11:30, 12:00-14:30, 16:00-17:00
# Wednesday: (no busy intervals given, hence free)
# Thursday: 9:30-10:00, 11:00-12:00, 14:30-15:30, 16:30-17:00
# Friday: 10:30-11:00, 11:30-12:00, 13:00-14:00, 15:00-15:30
linda_busy = {
    0: [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 11*60+30),
        (12*60, 13*60), (13*60+30, 14*60), (15*60, 15*60+30), (16*60, 17*60)],
    1: [(9*60, 11*60+30), (12*60, 14*60+30), (16*60, 17*60)],
    # Wednesday is free; no entry needed.
    3: [(9*60+30, 10*60), (11*60, 12*60), (14*60+30, 15*60+30), (16*60+30, 17*60)],
    4: [(10*60+30, 11*60), (11*60+30, 12*60), (13*60, 14*60), (15*60, 15*60+30)]
}

# Mark's busy intervals by day (times in minutes from midnight)
# Monday: 9:00-10:30, 11:00-14:30, 15:00-15:30, 16:00-17:00
# Tuesday: 9:00-10:30, 11:00-14:30, 15:00-17:00
# Wednesday: 9:00-17:00
# Thursday: 9:00-10:30, 11:00-11:30, 12:30-13:30, 14:30-15:00, 15:30-17:00
# Friday: 9:00-11:00, 11:30-17:00
mark_busy = {
    0: [(9*60, 10*60+30), (11*60, 14*60+30), (15*60, 15*60+30), (16*60, 17*60)],
    1: [(9*60, 10*60+30), (11*60, 14*60+30), (15*60, 17*60)],
    2: [(9*60, 17*60)],
    3: [(9*60, 10*60+30), (11*60, 11*60+30), (12*60+30, 13*60+30),
        (14*60+30, 15*60), (15*60+30, 17*60)],
    4: [(9*60, 11*60), (11*60+30, 17*60)]
}

# Preferences / Avoid constraints:
# Linda does NOT want to meet on Thursday (day 3) or Friday (day 4)
# Mark cannot meet on Monday (day 0)
linda_avoid = {3, 4}
mark_avoid = {0}

def no_overlap(busy_start, busy_end, meeting_start, dur):
    # Returns a condition ensuring the meeting [meeting_start, meeting_start+dur)
    # does not overlap with a busy interval [busy_start, busy_end)
    return Or(meeting_start + dur <= busy_start, meeting_start >= busy_end)

def find_earliest_meeting():
    # Iterate over days in order: Monday=0, Tuesday=1, Wednesday=2, Thursday=3, Friday=4
    for day in range(5):
        # If a participant avoids this day, skip it.
        if day in linda_avoid or day in mark_avoid:
            continue

        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight
        # Ensure meeting is within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Linda's busy constraints for this day (if any)
        if day in linda_busy:
            for bstart, bend in linda_busy[day]:
                solver.add(no_overlap(bstart, bend, s, duration))
                
        # Add Mark's busy constraints for this day (if any)
        if day in mark_busy:
            for bstart, bend in mark_busy[day]:
                solver.add(no_overlap(bstart, bend, s, duration))
                
        # Search for the earliest available minute on this day.
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