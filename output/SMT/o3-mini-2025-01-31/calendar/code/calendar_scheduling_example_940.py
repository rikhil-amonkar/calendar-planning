from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # duration in minutes for one hour
WORK_START = 9 * 60   # 9:00 in minutes (540)
WORK_END = 17 * 60    # 17:00 in minutes (1020)

# Day encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Megan's constraints: No meetings scheduled all week,
# but cannot meet on Wednesday (day 2).

# Kelly's busy intervals (times in minutes):
# Monday: 10:00 to 11:30, 13:00 to 14:00, 16:00 to 17:00
# Tuesday: 9:00 to 12:30, 13:00 to 17:00
# Wednesday: 10:00 to 11:30, 14:00 to 16:00, 16:30 to 17:00
# Thursday: 9:00 to 9:30, 10:00 to 11:00, 11:30 to 15:30, 16:00 to 16:30
# Friday: 9:00 to 10:00, 10:30 to 11:00, 11:30 to 13:00, 13:30 to 14:30, 15:00 to 17:00
kelly_busy = {
    0: [(10*60, 11*60+30), (13*60, 14*60), (16*60, 17*60)],
    1: [(9*60, 12*60+30), (13*60, 17*60)],
    2: [(10*60, 11*60+30), (14*60, 16*60), (16*60+30, 17*60)],
    3: [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 15*60+30), (16*60, 16*60+30)],
    4: [(9*60, 10*60), (10*60+30, 11*60), (11*60+30, 13*60), (13*60+30, 14*60+30), (15*60, 17*60)]
}

# Additional preference constraints:
# 1. Megan cannot meet on Wednesday (day 2).
# 2. Kelly would rather not meet on Monday after 14:00.
#    This preference will be enforced as a constraint for Monday meetings (i.e.
#    if the meeting is on Monday (day 0), then the meeting must start before 14:00).
PREFERENCE_MONDAY_END = 14 * 60  # 14:00 in minutes

def no_overlap(busy_start, busy_end, meeting_start, duration):
    # The meeting [meeting_start, meeting_start+duration) does not overlap with a busy interval
    # [busy_start, busy_end) if it finishes before the busy interval starts or starts after it ends.
    return Or(meeting_start + duration <= busy_start, meeting_start >= busy_end)

def find_earliest_meeting():
    # We know Megan does not do Wednesday, so skip day 2.
    candidate_days = [0, 1, 3, 4]  # Monday, Tuesday, Thursday, Friday

    # Try days in order (earliest availability)
    for day in candidate_days:
        # Create a solver for the day
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight on the chosen day
        
        # Constraint: meeting must be within working hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # If the day is Monday, enforce the preference: meeting must start before 14:00.
        if day == 0:
            solver.add(s < PREFERENCE_MONDAY_END)
        
        # Add Kelly's busy constraints if there are any for this day.
        if day in kelly_busy:
            for (busy_start, busy_end) in kelly_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Megan has no busy intervals, so no constraints for her, except she cannot meet on Wednesday (already excluded).
        
        # Try each minute of that day from WORK_START to WORK_END-duration:
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t   # Return the day and meeting start time in minutes
            solver.pop()
    return None, None

day, start_time = find_earliest_meeting()

if day is not None and start_time is not None:
    meeting_end = start_time + duration
    start_hour, start_min = divmod(start_time, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
          day_names[day], start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time found that satisfies all constraints.")