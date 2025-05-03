from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
WORK_START = 9 * 60    # 9:00 AM in minutes (540)
WORK_END = 17 * 60     # 17:00 in minutes (1020)

# Days mapping: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Christine's busy intervals (times in minutes)
# Tuesday: 16:30-17:00, Thursday: 9:00-10:00, Friday: 13:30-14:00
christine_busy = {
    1: [(16*60+30, 17*60)],     # Tuesday
    3: [(9*60, 10*60)],         # Thursday
    4: [(13*60+30, 14*60)]       # Friday
}

# Donna's busy intervals (times in minutes)
# Monday: 9:00-14:00, 14:30-16:30 
# Tuesday: 9:00-11:30, 13:00-14:30, 15:30-16:00 
# Wednesday: 9:00-9:30, 10:30-12:30, 13:30-14:30, 15:00-16:00 
# Thursday: 9:00-9:30, 10:00-11:30, 12:00-13:30, 14:00-17:00 
# Friday: 9:00-9:30, 11:00-12:00, 13:00-13:30, 14:00-14:30, 15:30-16:00, 16:30-17:00
donna_busy = {
    0: [(9*60, 14*60), (14*60+30, 16*60+30)],
    1: [(9*60, 11*60+30), (13*60, 14*60+30), (15*60+30, 16*60)],
    2: [(9*60, 9*60+30), (10*60+30, 12*60+30), (13*60+30, 14*60+30), (15*60, 16*60)],
    3: [(9*60, 9*60+30), (10*60, 11*60+30), (12*60, 13*60+30), (14*60, 17*60)],
    4: [(9*60, 9*60+30), (11*60, 12*60), (13*60, 13*60+30), (14*60, 14*60+30), (15*60+30, 16*60), (16*60+30, 17*60)]
}

# Donna does NOT want to meet on Wednesday (day 2)
donna_avoid = {2}

# Function to enforce that the meeting does not overlap a busy interval.
def no_overlap(busy_start, busy_end, meeting_start, dur):
    # Meeting interval [meeting_start, meeting_start+dur) must not overlap busy interval.
    return Or(meeting_start + dur <= busy_start, meeting_start >= busy_end)

def find_earliest_meeting():
    # Iterate in order Monday through Friday.
    for day in range(5):
        # Skip day if any participant avoids it.
        if day in donna_avoid:
            continue
        
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight
        
        # Meeting must fit within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Christine's busy constraints if any for that day.
        if day in christine_busy:
            for bstart, bend in christine_busy[day]:
                solver.add(no_overlap(bstart, bend, s, duration))
        
        # Add Donna's busy constraints for the day.
        if day in donna_busy:
            for bstart, bend in donna_busy[day]:
                solver.add(no_overlap(bstart, bend, s, duration))
        
        # Try each possible start time (minute granularity) in order.
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