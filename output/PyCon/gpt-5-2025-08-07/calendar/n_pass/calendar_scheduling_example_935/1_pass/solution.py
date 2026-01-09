# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

# Time helpers
def t(s):
    h, m = map(int, s.split(":"))
    return h * 60 + m

def to_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Work hours and meeting duration
WORK_START = t("09:00")
WORK_END = t("17:00")
MEETING_MIN = 30

days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
day_index = {d: i for i, d in enumerate(days)}

# Busy schedules (as provided)
terry_busy_str = {
    "Monday":    [("10:30", "11:00"), ("12:30", "14:00"), ("15:00", "17:00")],
    "Tuesday":   [("09:30", "10:00"), ("10:30", "11:00"), ("14:00", "14:30"), ("16:00", "16:30")],
    "Wednesday": [("09:30", "10:30"), ("11:00", "12:00"), ("13:00", "13:30"), ("15:00", "16:00"), ("16:30", "17:00")],
    "Thursday":  [("09:30", "10:00"), ("12:00", "12:30"), ("13:00", "14:30"), ("16:00", "16:30")],
    "Friday":    [("09:00", "11:30"), ("12:00", "12:30"), ("13:30", "16:00"), ("16:30", "17:00")],
}
frances_busy_str = {
    "Monday":    [("09:30", "11:00"), ("11:30", "13:00"), ("14:00", "14:30"), ("15:00", "16:00")],
    "Tuesday":   [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "12:00"), ("13:00", "14:30"), ("15:30", "16:30")],
    "Wednesday": [("09:30", "10:00"), ("10:30", "11:00"), ("11:30", "16:00"), ("16:30", "17:00")],
    "Thursday":  [("11:00", "12:30"), ("14:30", "17:00")],
    "Friday":    [("09:30", "10:30"), ("11:00", "12:30"), ("13:00", "16:00"), ("16:30", "17:00")],
}

# Convert to minute intervals
def convert_busy(busy_str):
    out = {}
    for d in days:
        intervals = busy_str.get(d, [])
        out[d] = [(t(s), t(e)) for s, e in intervals]
    return out

terry_busy = convert_busy(terry_busy_str)
frances_busy = convert_busy(frances_busy_str)

# Generate candidate start times on 30-min grid within work hours
start_times = []
curr = WORK_START
while curr + MEETING_MIN <= WORK_END:
    start_times.append(curr)
    curr += 30  # 30-minute increments

# Constraint problem
problem = Problem()
problem.addVariable("day", days)
problem.addVariable("start", start_times)

def is_free(day, start):
    end = start + MEETING_MIN
    if not (WORK_START <= start and end <= WORK_END):
        return False
    # Check Terry
    for bs, be in terry_busy[day]:
        if start < be and end > bs:  # overlap
            return False
    # Check Frances
    for bs, be in frances_busy[day]:
        if start < be and end > bs:  # overlap
            return False
    return True

problem.addConstraint(is_free, ("day", "start"))

solutions = problem.getSolutions()

if not solutions:
    print("No feasible solution found.")
else:
    # Preference: Avoid Tuesday if possible, then earliest availability.
    # Sort key: (is_tuesday, day_index, start_time)
    solutions.sort(key=lambda s: (1 if s["day"] == "Tuesday" else 0, day_index[s["day"]], s["start"]))
    best = solutions[0]
    day = best["day"]
    start = best["start"]
    end = start + MEETING_MIN
    start_str = to_str(start)
    end_str = to_str(end)
    time_range = f"{start_str}:{end_str}"
    # Output must include both the time range in braces and the day of the week
    print("{} {{{}}}".format(day, time_range))