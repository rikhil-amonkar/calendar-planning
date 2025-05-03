from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
WORK_START = 9 * 60    # 9:00 AM in minutes (540)
WORK_END = 17 * 60     # 17:00 in minutes (1020)

# Days mapping: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Henry's busy intervals (times in minutes)
# Monday: 9:00-9:30, 10:00-11:00
# Tuesday: 10:30-11:00, 14:30-15:30
# Wednesday: 9:00-10:30, 11:30-12:30, 13:00-14:30, 15:00-16:00, 16:30-17:00
# Thursday: 9:00-9:30, 10:00-11:00, 11:30-12:30, 13:30-15:00, 15:30-16:00
# Friday: 9:30-10:00, 11:30-12:00, 14:00-14:30, 15:30-16:00
henry_busy = {
    0: [(9*60, 9*60+30), (10*60, 11*60)],
    1: [(10*60+30, 11*60), (14*60+30, 15*60+30)],
    2: [(9*60, 10*60+30), (11*60+30, 12*60+30), (13*60, 14*60+30), (15*60, 16*60), (16*60+30, 17*60)],
    3: [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 12*60+30), (13*60+30, 15*60), (15*60+30, 16*60)],
    4: [(9*60+30, 10*60), (11*60+30, 12*60), (14*60, 14*60+30), (15*60+30, 16*60)]
}

# Jacqueline's busy intervals (times in minutes)
# Monday: 9:00-11:30, 12:00-14:00, 14:30-15:30, 16:00-17:00
# Tuesday: 9:30-10:30, 11:00-11:30, 12:00-13:00, 13:30-14:30, 15:00-17:00
# Wednesday: 9:00-11:00, 11:30-17:00
# Thursday: 9:00-9:30, 10:30-13:00, 13:30-14:00, 14:30-16:00, 16:30-17:00
# Friday: 9:00-17:00
jacqueline_busy = {
    0: [(9*60, 11*60+30), (12*60, 14*60), (14*60+30, 15*60+30), (16*60, 17*60)],
    1: [(9*60+30, 10*60+30), (11*60, 11*60+30), (12*60, 13*60), (13*60+30, 14*60+30), (15*60, 17*60)],
    2: [(9*60, 11*60), (11*60+30, 17*60)],
    3: [(9*60, 9*60+30), (10*60+30, 13*60), (13*60+30, 14*60), (14*60+30, 16*60), (16*60+30, 17*60)],
    4: [(9*60, 17*60)]
}

# Avoid constraints:
# Henry cannot meet on Tuesday (1) or Thursday (3)
henry_avoid = {1, 3}
# Jacqueline cannot meet on Monday (0)
jacqueline_avoid = {0}

# Function to enforce that the meeting does not overlap a busy interval.
def no_overlap(busy_start, busy_end, meeting_start, dur):
    # The meeting interval [meeting_start, meeting_start+dur) should not overlap the busy interval [busy_start, busy_end)
    return Or(meeting_start + dur <= busy_start, meeting_start >= busy_end)

def find_earliest_meeting():
    # Iterate through days Monday(0) to Friday(4)
    for day in range(5):
        # Skip day if any participant avoids it.
        if day in henry_avoid or day in jacqueline_avoid:
            continue
        
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight
        
        # The meeting must be within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Henry's busy constraints for the day (if any)
        if day in henry_busy:
            for bstart, bend in henry_busy[day]:
                solver.add(no_overlap(bstart, bend, s, duration))
                
        # Add Jacqueline's busy constraints for the day (if any)
        if day in jacqueline_busy:
            for bstart, bend in jacqueline_busy[day]:
                solver.add(no_overlap(bstart, bend, s, duration))
        
        # Now search for the earliest available minute that satisfies the constraints.
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