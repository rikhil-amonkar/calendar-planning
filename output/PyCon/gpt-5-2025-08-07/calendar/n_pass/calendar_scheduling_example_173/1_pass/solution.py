from constraint import Problem, AllEqualConstraint

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt_minutes(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Meeting details
day_of_week = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30  # minutes

# Participants' busy schedules (inclusive of start, exclusive of end)
busy_str = {
    "Jacqueline": [("09:00", "09:30"), ("11:00", "11:30"), ("12:30", "13:00"), ("15:30", "16:00")],
    "Harold":     [("10:00", "10:30"), ("13:00", "13:30"), ("15:00", "17:00")],
    "Arthur":     [("09:00", "09:30"), ("10:00", "12:30"), ("14:30", "15:00"), ("15:30", "17:00")],
    "Kelly":      [("09:00", "09:30"), ("10:00", "11:00"), ("11:30", "12:30"), ("14:00", "15:00"), ("15:30", "16:00")],
}

# Convert busy schedules to minutes
busy = {}
for person, intervals in busy_str.items():
    busy[person] = [(to_minutes(s), to_minutes(e)) for s, e in intervals]

# Candidate start times in 30-minute increments within work hours
candidates = list(range(work_start, work_end - duration + 1, duration))

def is_free(start, intervals, dur):
    end = start + dur
    for bs, be in intervals:
        # overlap if start < be and end > bs
        if start < be and end > bs:
            return False
    return True

# Build availability domains
domains = {}
for person in busy:
    domains[person] = [t for t in candidates if is_free(t, busy[person], duration)]

# Harold does not want to meet after 13:00 => meeting must not extend beyond 13:00
latest_end_for_harold = to_minutes("13:00")
domains["Harold"] = [t for t in domains["Harold"] if t + duration <= latest_end_for_harold]

# Set up the constraint problem
problem = Problem()
for person, domain in domains.items():
    problem.addVariable(person, domain)

# All participants must have the same start time
problem.addConstraint(AllEqualConstraint(), list(domains.keys()))

solutions = problem.getSolutions()

if not solutions:
    raise SystemExit("No feasible meeting time found.")

# Choose the earliest feasible start time
best_solution = min(solutions, key=lambda sol: sol["Harold"])  # all equal, any key works
start = best_solution["Harold"]
end = start + duration

# Output in required formats
print("{" + f"{fmt_minutes(start)}:{fmt_minutes(end)}" + "}")
print(day_of_week)