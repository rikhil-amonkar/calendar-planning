from constraint import Problem

# Meeting details
DURATION_MIN = 30  # 30 minutes
WORK_START = 9 * 60
WORK_END = 17 * 60

# Days under consideration
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
day_order = {d: i for i, d in enumerate(days)}
prefer_days = {"Monday", "Tuesday"}  # Cheryl would rather not meet Wed/Thu

# Participants' busy calendars (in minutes from midnight)
def t(h, m=0):
    return h * 60 + m

james_busy = {
    "Monday":    [(t(9,0), t(9,30)), (t(10,30), t(11,0)), (t(12,30), t(13,0)),
                  (t(14,30), t(15,30)), (t(16,30), t(17,0))],
    "Tuesday":   [(t(9,0), t(11,0)), (t(11,30), t(12,0)), (t(12,30), t(15,30)),
                  (t(16,0), t(17,0))],
    "Wednesday": [(t(10,0), t(11,0)), (t(12,0), t(13,0)), (t(13,30), t(16,0))],
    "Thursday":  [(t(9,30), t(11,30)), (t(12,0), t(12,30)), (t(13,0), t(13,30)),
                  (t(14,0), t(14,30)), (t(16,30), t(17,0))],
}

# Cheryl is wide open all week; preference handled in selection step

def overlaps(start, end, intervals):
    for s, e in intervals:
        if start < e and end > s:
            return True
    return False

# Build domains
start_times = list(range(WORK_START, WORK_END - DURATION_MIN + 1, 30))

# Set up constraint problem
problem = Problem()
problem.addVariable("day", days)
problem.addVariable("start", start_times)

def meeting_feasible(day, start):
    end = start + DURATION_MIN
    # Within work hours (already guaranteed by domain, but keep for clarity)
    if not (WORK_START <= start and end <= WORK_END):
        return False
    # No conflicts for James
    if overlaps(start, end, james_busy.get(day, [])):
        return False
    # Cheryl is free all week (no hard constraints)
    return True

problem.addConstraint(meeting_feasible, ("day", "start"))

solutions = problem.getSolutions()

if not solutions:
    raise SystemExit("No feasible meeting found.")

# Preference-aware earliest selection:
# - Prefer Monday and Tuesday over Wednesday and Thursday
# - Earliest day, then earliest time
def pref_key(sol):
    day = sol["day"]
    start = sol["start"]
    pref_tier = 0 if day in prefer_days else 1
    return (pref_tier, day_order[day], start)

best = min(solutions, key=pref_key)
best_day = best["day"]
start = best["start"]
end = start + DURATION_MIN

def fmt(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

start_str = fmt(start)
end_str = fmt(end)

# Output both time range and day (e.g., Monday {14:30:15:30})
print(f"{best_day} {{{start_str}:{end_str}}}")