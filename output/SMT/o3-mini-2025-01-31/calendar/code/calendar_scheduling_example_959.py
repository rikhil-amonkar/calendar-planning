from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30                  # meeting duration in minutes
WORK_START = 9 * 60            # work hours start at 09:00 (in minutes: 540)
WORK_END = 17 * 60             # work hours end at 17:00 (in minutes: 1020)

# Mapping for day names: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Kelly's busy intervals (in minutes):
# Tuesday: 9:00 to 9:30 -> (540, 570)
# Friday:  9:00 to 9:30 -> (540, 570)
kelly_busy = {
    1: [(9 * 60, 9 * 60 + 30)],
    4: [(9 * 60, 9 * 60 + 30)]
}

# Patricia's busy intervals (in minutes):
# Monday:    9:30 to 16:00 and 16:30 to 17:00 -> [(570, 960), (990, 1020)]
# Tuesday:   9:00 to 11:00 and 12:30 to 16:30   -> [(540, 660), (750, 990)]
# Wednesday: 10:00 to 11:00, 11:30 to 12:00, 12:30 to 14:00, 14:30 to 17:00
#            -> [(600,660), (690,720), (750,840), (870,1020)]
# Thursday:  9:00 to 10:30, 11:00 to 12:30, 13:30 to 14:30, 15:00 to 15:30, 16:00 to 17:00
#            -> [(540,630), (660,750), (810,870), (900,930), (960,1020)]
# Friday:    9:00 to 10:00, 10:30 to 11:30, 12:00 to 14:00, 14:30 to 16:00, 16:30 to 17:00
#            -> [(540,600), (630,690), (720,840), (870,960), (990,1020)]
patricia_busy = {
    0: [(9 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)],
    1: [(9 * 60, 11 * 60), (12 * 60 + 30, 16 * 60 + 30)],
    2: [(10 * 60, 11 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 14 * 60), (14 * 60 + 30, 17 * 60)],
    3: [(9 * 60, 10 * 60 + 30), (11 * 60, 12 * 60 + 30), (13 * 60 + 30, 14 * 60 + 30), (15 * 60, 15 * 60 + 30), (16 * 60, 17 * 60)],
    4: [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60 + 30), (12 * 60, 14 * 60), (14 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)]
}

# Avoid constraints:
# Patricia would like to avoid more meetings on Monday.
# We model this as avoiding scheduling on Monday (day 0) for Patricia.
patricia_avoid = {0}
# Kelly does not have an avoid constraint.
kelly_avoid = set()

def no_overlap(busy_start, busy_end, s, dur):
    # Returns a constraint that ensures the meeting [s, s+dur) does not overlap with [busy_start, busy_end)
    return Or(s + dur <= busy_start, s >= busy_end)

def find_earliest_meeting():
    # Iterate over the days Monday (0) to Friday (4)
    for day in range(5):
        # If any participant's avoid constraint excludes this day, then skip it.
        if day in patricia_avoid or day in kelly_avoid:
            continue

        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight
        
        # Ensure the meeting is within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Kelly's busy constraints for the day if any.
        if day in kelly_busy:
            for start_busy, end_busy in kelly_busy[day]:
                solver.add(no_overlap(start_busy, end_busy, s, duration))
        
        # Add Patricia's busy constraints for the day if any.
        if day in patricia_busy:
            for start_busy, end_busy in patricia_busy[day]:
                solver.add(no_overlap(start_busy, end_busy, s, duration))
        
        # Check minute-by-minute starting at the earliest work time for a valid meeting time.
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