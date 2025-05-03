from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # half an hour meeting in minutes
WORK_START = 9 * 60    # work day starts at 9:00 (in minutes)
WORK_END = 17 * 60     # work day ends at 17:00 (in minutes)

# Day encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Virginia's busy intervals (in minutes from midnight)
# Monday: 9:30-10:00, 12:00-12:30, 14:30-15:00, 16:30-17:00
# Tuesday: 9:00-10:30, 11:00-11:30, 13:30-14:30, 15:30-16:00
# Wednesday: 10:00-12:00, 13:00-13:30, 14:30-15:00, 16:00-17:00
# Thursday: 9:00-9:30, 10:00-11:00, 13:00-14:00, 14:30-16:00, 16:30-17:00
# Friday: 9:30-10:30, 12:00-13:00, 13:30-15:30, 16:00-17:00
virginia_busy = {
    0: [(9*60+30, 10*60), (12*60, 12*60+30), (14*60+30, 15*60), (16*60+30, 17*60)],
    1: [(9*60, 10*60+30), (11*60, 11*60+30), (13*60+30, 14*60+30), (15*60+30, 16*60)],
    2: [(10*60, 12*60), (13*60, 13*60+30), (14*60+30, 15*60), (16*60, 17*60)],
    3: [(9*60, 9*60+30), (10*60, 11*60), (13*60, 14*60), (14*60+30, 16*60), (16*60+30, 17*60)],
    4: [(9*60+30, 10*60+30), (12*60, 13*60), (13*60+30, 15*60+30), (16*60, 17*60)]
}

# Maria's busy intervals (in minutes from midnight)
# Monday: 9:00-10:30, 11:30-15:30, 16:00-17:00
# Tuesday: 9:00-10:00, 12:00-15:30, 16:00-16:30
# Wednesday: 9:30-12:00, 13:00-13:30, 14:00-15:30, 16:00-17:00
# Thursday: 9:30-11:00, 12:00-15:30, 16:00-17:00
# Friday: 10:30-11:30, 12:00-12:30, 13:30-14:00, 14:30-16:30
maria_busy = {
    0: [(9*60, 10*60+30), (11*60+30, 15*60+30), (16*60, 17*60)],
    1: [(9*60, 10*60), (12*60, 15*60+30), (16*60, 16*60+30)],
    2: [(9*60+30, 12*60), (13*60, 13*60+30), (14*60, 15*60+30), (16*60, 17*60)],
    3: [(9*60+30, 11*60), (12*60, 15*60+30), (16*60, 17*60)],
    4: [(10*60+30, 11*60+30), (12*60, 12*60+30), (13*60+30, 14*60), (14*60+30, 16*60+30)]
}

# Preferences:
# Virginia would rather not meet on Monday, Tuesday, Thursday or Friday
allowed_days_virginia = {2}  # Only Wednesday is acceptable
# Maria does not want to meet on Wednesday after 13:30.
# We'll enforce that if meeting is scheduled on Wednesday (day 2),
# then the meeting must finish by 13:30 (i.e., start + duration <= 13:30)
allowed_days_maria = {0, 1, 2, 3, 4}  # no day exclusion, just a time constraint on Wed

# The meeting day must be in the intersection of allowed days.
allowed_days = sorted(list(allowed_days_virginia.intersection(allowed_days_maria)))
# This forces day to be Wednesday (day 2)

# Helper function to ensure that meeting [s, s+duration] does not overlap a busy interval [busy_start, busy_end]
def no_overlap(busy_start, busy_end, meeting_start, duration):
    return Or(meeting_start + duration <= busy_start, meeting_start >= busy_end)

def find_earliest_meeting():
    for day in allowed_days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight
        
        # Meeting must be within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # If the day is Wednesday and Maria’s preference applies:
        if day == 2:
            # The meeting must finish by 13:30 (i.e., 13*60+30 = 810 min)
            solver.add(s + duration <= 13*60 + 30)
        
        # Add Virginia's busy intervals constraints if any for this day.
        if day in virginia_busy:
            for (busy_start, busy_end) in virginia_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Add Maria's busy intervals constraints for this day.
        if day in maria_busy:
            for (busy_start, busy_end) in maria_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Iterate over possible start times (minute resolution) and return earliest that satisfies all constraints.
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
    sh, sm = divmod(start_time, 60)
    eh, em = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
          day_names[day], sh, sm, eh, em))
else:
    print("No valid meeting time found that satisfies all constraints.")