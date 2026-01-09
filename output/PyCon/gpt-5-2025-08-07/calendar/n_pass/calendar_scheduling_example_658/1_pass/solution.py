from constraint import Problem

def t(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Meeting parameters
duration = 30  # minutes
days = ["Monday", "Tuesday"]
work_start = t("09:00")
work_end = t("17:00")
start_times = [m for m in range(work_start, work_end - duration + 1, 30)]

# Busy schedules in minutes since 00:00
busy = {
    "Shirley": {
        "Monday": [(t("10:30"), t("11:00")), (t("12:00"), t("12:30")), (t("16:00"), t("16:30"))],
        "Tuesday": [(t("09:30"), t("10:00"))],
    },
    "Albert": {
        "Monday": [(t("09:00"), t("17:00"))],
        "Tuesday": [(t("09:30"), t("11:00")), (t("11:30"), t("12:30")), (t("13:00"), t("16:00")), (t("16:30"), t("17:00"))],
    },
}

def no_overlap(start, end, intervals):
    for s, e in intervals:
        if start < e and end > s:
            return False
    return True

def valid(day, start):
    end = start + duration
    if not (work_start <= start and end <= work_end):
        return False
    # Check all participants' busy times on the chosen day
    for person in busy:
        if not no_overlap(start, end, busy[person][day]):
            return False
    return True

# Build CSP
problem = Problem()
problem.addVariable("day", days)
problem.addVariable("start", start_times)
problem.addConstraint(valid, ("day", "start"))

solutions = problem.getSolutions()

if not solutions:
    raise SystemExit("No feasible meeting time found.")

# Preference: Shirley would rather not meet on Tuesday after 10:30 (i.e., prefer start <= 10:30 on Tuesday)
pref_cutoff = t("10:30")
def preferred(sol):
    return sol["day"] != "Tuesday" or sol["start"] <= pref_cutoff

preferred_solutions = [s for s in solutions if preferred(s)]
candidates = preferred_solutions if preferred_solutions else solutions

day_order = {"Monday": 0, "Tuesday": 1}
best = sorted(candidates, key=lambda s: (day_order[s["day"]], s["start"]))[0]

start = best["start"]
end = start + duration
day = best["day"]

# Output day and time range in required format
print(day)
print(f"{{{fmt(start)}:{fmt(end)}}}")