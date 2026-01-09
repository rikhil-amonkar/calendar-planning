# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_str(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Working hours and meeting duration
WORK_START = to_minutes("09:00")
WORK_END = to_minutes("17:00")
DURATION = 60

# Days to consider
days = ["Monday", "Tuesday", "Wednesday"]

# Busy schedules (inclusive of start, exclusive of end)
busy = {
    "Stephanie": {
        "Monday":    [(to_minutes("09:30"), to_minutes("10:00")),
                      (to_minutes("10:30"), to_minutes("11:00")),
                      (to_minutes("11:30"), to_minutes("12:00")),
                      (to_minutes("14:00"), to_minutes("14:30"))],
        "Tuesday":   [(to_minutes("12:00"), to_minutes("13:00"))],
        "Wednesday": [(to_minutes("09:00"), to_minutes("10:00")),
                      (to_minutes("13:00"), to_minutes("14:00"))],
    },
    "Betty": {
        "Monday":    [(to_minutes("09:00"), to_minutes("10:00")),
                      (to_minutes("11:00"), to_minutes("11:30")),
                      (to_minutes("14:30"), to_minutes("15:00")),
                      (to_minutes("15:30"), to_minutes("16:00"))],
        "Tuesday":   [(to_minutes("09:00"), to_minutes("09:30")),
                      (to_minutes("11:30"), to_minutes("12:00")),
                      (to_minutes("12:30"), to_minutes("14:30")),
                      (to_minutes("15:30"), to_minutes("16:00"))],
        "Wednesday": [(to_minutes("10:00"), to_minutes("11:30")),
                      (to_minutes("12:00"), to_minutes("14:00")),
                      (to_minutes("14:30"), to_minutes("17:00"))],
    }
}

# Generate 30-minute start times within working hours so meeting ends by WORK_END
start_times = list(range(WORK_START, WORK_END - DURATION + 1, 30))

def is_free_for_all(day, start):
    end = start + DURATION
    # Ensure within working hours
    if start < WORK_START or end > WORK_END:
        return False

    # Betty cannot meet on Tuesday after 12:30 => meeting must end by 12:30 on Tuesday
    if day == "Tuesday":
        if end > to_minutes("12:30"):
            return False

    # Check overlaps against each participant's busy schedule
    for person in busy:
        for (bs, be) in busy[person].get(day, []):
            # Overlap if intervals intersect
            if not (end <= bs or start >= be):
                return False
    return True

# Set up constraint problem
problem = Problem()
problem.addVariable("day", days)
problem.addVariable("start", start_times)

# Feasibility constraint
problem.addConstraint(lambda d, s: is_free_for_all(d, s), ("day", "start"))

solutions = problem.getSolutions()

if not solutions:
    # As per prompt, a solution exists; this is a safeguard.
    raise RuntimeError("No feasible meeting time found.")

# Preference: avoid Monday for Stephanie if possible.
# Choose earliest time among preferred days; if none, fallback to Monday.
def pref_key(sol):
    # 0 for preferred (not Monday), 1 for Monday
    avoid_monday = 0 if sol["day"] != "Monday" else 1
    return (avoid_monday, sol["start"])

solutions.sort(key=pref_key)
chosen = solutions[0]
start = chosen["start"]
end = start + DURATION

# Output: day and time range in {HH:MM:HH:MM}
print(chosen["day"])
print(f"{{{to_str(start)}:{to_str(end)}}}")