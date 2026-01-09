from constraint import Problem

# Meeting parameters
MEETING_DURATION_MIN = 60  # 1 hour
WORK_START = 9 * 60
WORK_END = 17 * 60

days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
start_times = list(range(WORK_START, WORK_END - MEETING_DURATION_MIN + 1, 30))  # every 30 min from 09:00 to 16:00

def to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt(mins):
    return f"{mins // 60:02d}:{mins % 60:02d}"

# Busy schedules
bryan_busy = {
    "Thursday": [(to_min("09:30"), to_min("10:00")), (to_min("12:30"), to_min("13:00"))],
    "Friday":   [(to_min("10:30"), to_min("11:00")), (to_min("14:00"), to_min("14:30"))],
}

nicholas_busy = {
    "Monday":    [(to_min("11:30"), to_min("12:00")), (to_min("13:00"), to_min("15:30"))],
    "Tuesday":   [(to_min("09:00"), to_min("09:30")), (to_min("11:00"), to_min("13:30")), (to_min("14:00"), to_min("16:30"))],
    "Wednesday": [(to_min("09:00"), to_min("09:30")), (to_min("10:00"), to_min("11:00")), (to_min("11:30"), to_min("13:30")),
                  (to_min("14:00"), to_min("14:30")), (to_min("15:00"), to_min("16:30"))],
    "Thursday":  [(to_min("10:30"), to_min("11:30")), (to_min("12:00"), to_min("12:30")), (to_min("15:00"), to_min("15:30")),
                  (to_min("16:30"), to_min("17:00"))],
    "Friday":    [(to_min("09:00"), to_min("10:30")), (to_min("11:00"), to_min("12:00")), (to_min("12:30"), to_min("14:30")),
                  (to_min("15:30"), to_min("16:00")), (to_min("16:30"), to_min("17:00"))],
}

# Preferences (soft constraints)
preferences = {
    "Bryan": {"avoid_days": {"Tuesday"}},
    "Nicholas": {"avoid_days": {"Monday", "Thursday"}},
}

def overlaps(start, end, busy_list):
    for b_start, b_end in busy_list:
        if start < b_end and end > b_start:  # overlap if intervals intersect
            return True
    return False

def availability_constraint(day, start):
    end = start + MEETING_DURATION_MIN
    if end > WORK_END:
        return False
    bryan_day_busy = bryan_busy.get(day, [])
    nicholas_day_busy = nicholas_busy.get(day, [])
    if overlaps(start, end, bryan_day_busy):
        return False
    if overlaps(start, end, nicholas_day_busy):
        return False
    return True

# Build CSP
problem = Problem()
problem.addVariable("day", days)
problem.addVariable("start", start_times)
problem.addConstraint(availability_constraint, ("day", "start"))

solutions = problem.getSolutions()

if not solutions:
    print("No solution found")
else:
    def penalty(sol):
        day = sol["day"]
        p = 0
        if day in preferences["Bryan"]["avoid_days"]:
            p += 1
        if day in preferences["Nicholas"]["avoid_days"]:
            p += 1
        return p

    # Choose solution minimizing preference penalty, then earliest time, then day order
    day_index = {d: i for i, d in enumerate(days)}
    solutions.sort(key=lambda s: (penalty(s), s["start"], day_index[s["day"]]))
    best = solutions[0]
    start = best["start"]
    end = start + MEETING_DURATION_MIN
    time_range = f"{fmt(start)}:{fmt(end)}"
    print(f"{{{time_range}}}")
    print(best["day"])