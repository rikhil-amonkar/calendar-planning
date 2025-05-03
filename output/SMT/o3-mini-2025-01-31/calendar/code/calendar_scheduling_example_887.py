from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30           # meeting duration in minutes (half an hour)
WORK_START = 9 * 60     # Start of work day: 9:00 → 540 minutes
WORK_END   = 17 * 60    # End of work day: 17:00 → 1020 minutes

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday.
candidate_days = [0, 1, 2, 3]

# Busy intervals for Nancy, given as (start, end) in minutes.
# Nancy:
#   Monday: 11:00 to 11:30 -> (11*60, 11*60+30) => (660, 690)
#   Tuesday: no meetings
#   Wednesday: 9:30 to 10:00 -> (570, 600), and 12:00 to 12:30 -> (720, 750)
#   Thursday: 14:00 to 14:30 -> (840, 870)
nancy_busy = {
    0: [(11*60, 11*60+30)],
    1: [],  # no meetings on Tuesday
    2: [(9*60+30, 10*60), (12*60, 12*60+30)],
    3: [(14*60, 14*60+30)]
}

# Busy intervals for Theresa:
#   Monday: 9:00 to 10:30 -> (540, 630), 11:30 to 12:00 -> (690, 720),
#           14:30 to 15:00 -> (870, 900), 15:30 to 16:00 -> (930, 960)
#   Tuesday: 9:00 to 9:30 -> (540, 570), 10:00 to 11:00 -> (600, 660),
#            11:30 to 12:30 -> (690, 750), 14:00 to 14:30 -> (840, 870),
#            15:30 to 16:00 -> (930, 960)
#   Wednesday: 9:00 to 9:30 -> (540, 570), 10:30 to 13:00 -> (630, 780),
#              14:00 to 16:00 -> (840, 960), 16:30 to 17:00 -> (990, 1020)
#   Thursday: 9:30 to 11:30 -> (570, 690), 12:00 to 17:00 -> (720, 1020)
theresa_busy = {
    0: [(540, 630), (690, 720), (870, 900), (930, 960)],
    1: [(540, 570), (600, 660), (690, 750), (840, 870), (930, 960)],
    2: [(540, 570), (630, 780), (840, 960), (990, 1020)],
    3: [(570, 690), (720, 1020)]
}

# Utility function: returns a constraint that the meeting starting at 's' (with duration 'duration')
# does NOT overlap with a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Search for the earliest meeting time that satisfies all constraints on the candidate days.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes after midnight
        
        # Meeting must lie completely within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add constraints for Nancy's busy intervals for the chosen day.
        for busy_start, busy_end in nancy_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Add constraints for Theresa's busy intervals for the chosen day.
        for busy_start, busy_end in theresa_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Try every possible start minute from WORK_START to WORK_END-duration.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

day, t = find_meeting_time(candidate_days)

if day is not None:
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    selected_day_name = day_names[day]
    start_hour, start_minute = divmod(t, 60)
    end_hour, end_minute = divmod(t + duration, 60)
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}.".format(
        selected_day_name, start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")