# Requires: python-constraint
from constraint import Problem

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Work hours and meeting duration
WORK_START = 9 * 60
WORK_END = 17 * 60
MEETING_DURATION = 60  # minutes

days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Busy schedules in minutes from 00:00, intervals are [start, end)
diane_busy = {
    "Monday":    [(12*60, 12*60+30), (15*60, 15*60+30)],
    "Tuesday":   [(10*60, 11*60), (11*60+30, 12*60), (12*60+30, 13*60), (16*60, 17*60)],
    "Wednesday": [(9*60, 9*60+30), (14*60+30, 15*60), (16*60+30, 17*60)],
    "Thursday":  [(15*60+30, 16*60+30)],
    "Friday":    [(9*60+30, 11*60+30), (14*60+30, 15*60), (16*60, 17*60)],
}

matthew_busy = {
    "Monday":    [(9*60, 10*60), (10*60+30, 17*60)],
    "Tuesday":   [(9*60, 17*60)],
    "Wednesday": [(9*60, 11*60), (12*60, 14*60+30), (16*60, 17*60)],
    "Thursday":  [(9*60, 16*60)],
    "Friday":    [(9*60, 17*60)],
}

def overlaps(start1, end1, start2, end2):
    return max(start1, start2) < min(end1, end2)

def is_free_for(day, start, busy):
    end = start + MEETING_DURATION
    # Within work hours
    if start < WORK_START or end > WORK_END:
        return False
    # No overlap with busy intervals
    for b_start, b_end in busy.get(day, []):
        if overlaps(start, end, b_start, b_end):
            return False
    return True

def availability_constraint(day, start):
    return is_free_for(day, start, diane_busy) and is_free_for(day, start, matthew_busy)

# Build constraint problem
problem = Problem()
problem.addVariable("day", days)
# 30-minute increments for start times between 09:00 and 16:00 inclusive
start_times = list(range(WORK_START, WORK_END - MEETING_DURATION + 1, 30))
problem.addVariable("start", start_times)
problem.addConstraint(availability_constraint, ("day", "start"))

solutions = problem.getSolutions()

if not solutions:
    raise SystemExit("No feasible meeting time found.")

# Preference: Matthew would rather not meet on Wednesday before 12:30
def respects_preference(sol):
    return not (sol["day"] == "Wednesday" and sol["start"] < (12*60 + 30))

day_order = {d: i for i, d in enumerate(days)}

solutions.sort(key=lambda s: (0 if respects_preference(s) else 1,
                              day_order[s["day"]],
                              s["start"]))

chosen = solutions[0]
start = chosen["start"]
end = start + MEETING_DURATION

# Output: day of week and {HH:MM:HH:MM}
print(chosen["day"])
print(f"{{{fmt_time(start)}:{fmt_time(end)}}}")