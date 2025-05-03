from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # minutes for the meeting
WORK_START = 9 * 60    # 9:00 AM in minutes (540)
WORK_END = 17 * 60     # 17:00 in minutes (1020)

# Days of the week: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Busy intervals for Diane (times in minutes from midnight)
# Monday: 12:30-13:30, 14:00-14:30, 15:00-15:30, 16:30-17:00
# Tuesday: 9:00-9:30, 10:00-12:00, 12:30-14:00, 14:30-15:30, 16:00-16:30
# Wednesday: 10:30-11:00, 11:30-12:00, 12:30-13:30, 15:00-17:00
# Thursday: 10:00-10:30, 11:00-11:30, 12:00-15:00, 15:30-16:00
# Friday: 9:30-10:00, 10:30-11:00, 13:00-13:30, 14:00-14:30, 16:30-17:00
diane_busy = {
    0: [(12*60+30, 13*60+30), (14*60, 14*60+30), (15*60, 15*60+30), (16*60+30, 17*60)],
    1: [(9*60, 9*60+30), (10*60, 12*60), (12*60+30, 14*60), (14*60+30, 15*60+30), (16*60, 16*60+30)],
    2: [(10*60+30, 11*60), (11*60+30, 12*60), (12*60+30, 13*60+30), (15*60, 17*60)],
    3: [(10*60, 10*60+30), (11*60, 11*60+30), (12*60, 15*60), (15*60+30, 16*60)],
    4: [(9*60+30, 10*60), (10*60+30, 11*60), (13*60, 13*60+30), (14*60, 14*60+30), (16*60+30, 17*60)]
}

# Busy intervals for Christian
# Monday: 9:00-17:00 (busy all day)
# Tuesday: 10:00-11:30, 12:00-12:30, 13:00-16:30
# Wednesday: 9:00-17:00
# Thursday: 9:00-16:00, 16:30-17:00
# Friday: 9:00-14:30, 15:00-15:30, 16:00-17:00
christian_busy = {
    0: [(9*60, 17*60)],
    1: [(10*60, 11*60+30), (12*60, 12*60+30), (13*60, 16*60+30)],
    2: [(9*60, 17*60)],
    3: [(9*60, 16*60), (16*60+30, 17*60)],
    4: [(9*60, 14*60+30), (15*60, 15*60+30), (16*60, 17*60)]
}

# Preferences: avoid meeting on certain days:
# Diane would like to avoid more meetings on Thursday (day 3)
# Christian would like to avoid more meetings on Tuesday (day 1)
diane_avoid = {3}         # Avoid Thursday
christian_avoid = {1}     # Avoid Tuesday

def no_overlap(busy_start, busy_end, meeting_start, dur):
    # No overlap means meeting ends before busy starts OR meeting starts
    # at/after busy ends.
    return Or(meeting_start + dur <= busy_start, meeting_start >= busy_end)

def find_earliest_meeting():
    # Iterate days in order: Monday (0), Tuesday (1), Wednesday (2),
    # Thursday (3), Friday (4)
    # But we skip days that are to be avoided by the respective participants.
    for day in range(5):
        # Skip day if a participant prefers to avoid it.
        if day in diane_avoid or day in christian_avoid:
            continue

        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight
        # Enforce meeting within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add Diane's busy constraints for this day.
        if day in diane_busy:
            for bstart, bend in diane_busy[day]:
                solver.add(no_overlap(bstart, bend, s, duration))

        # Add Christian's busy constraints for this day.
        if day in christian_busy:
            for bstart, bend in christian_busy[day]:
                solver.add(no_overlap(bstart, bend, s, duration))

        # Iterate through each possible start time to find the earliest available.
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