from constraint import Problem

# Helper functions
def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def add_minutes(t, mins):
    total = to_minutes(t) + mins
    h = total // 60
    m = total % 60
    return f"{h:02d}:{m:02d}"

def overlaps(s_start, s_end, b_start, b_end):
    return max(s_start, b_start) < min(s_end, b_end)

def compute_blocked_starts(start_times, intervals):
    blocked = set()
    for s in start_times:
        s_min = to_minutes(s)
        e_min = s_min + 30
        for a, b in intervals:
            if overlaps(s_min, e_min, to_minutes(a), to_minutes(b)):
                blocked.add(s)
                break
    return blocked

# Work hours and discretized start times (30-minute increments)
start_times = [
    "09:00","09:30","10:00","10:30","11:00","11:30",
    "12:00","12:30","13:00","13:30","14:00","14:30",
    "15:00","15:30","16:00","16:30"
]
days = ["Monday", "Tuesday", "Wednesday"]

# Participants' busy schedules
busy = {
    "Tyler": {
        "Monday": [],
        "Tuesday": [("09:00","09:30"), ("14:30","15:00")],
        "Wednesday": [("10:30","11:00"), ("12:30","13:00"), ("13:30","14:00"), ("16:30","17:00")],
    },
    "Ruth": {
        "Monday": [("09:00","10:00"), ("10:30","12:00"), ("12:30","14:30"), ("15:00","16:00"), ("16:30","17:00")],
        "Tuesday": [("09:00","17:00")],
        "Wednesday": [("09:00","17:00")],
    }
}

# Precompute blocked start times for each person/day
blocked_map = {person: {} for person in busy}
for person, sched in busy.items():
    for d in days:
        intervals = sched.get(d, [])
        blocked_map[person][d] = compute_blocked_starts(start_times, intervals)

# Set up the CSP
problem = Problem()
problem.addVariable("day", days)
problem.addVariable("start", start_times)

# Availability constraints for both Tyler and Ruth
def availability_constraint(day, start):
    return all(start not in blocked_map[person][day] for person in ["Tyler", "Ruth"])

problem.addConstraint(availability_constraint, ("day", "start"))

# Preference: Tyler would like to avoid Monday before 16:00
def preference_constraint(day, start):
    if day == "Monday":
        return start in {"16:00", "16:30"}
    return True

problem.addConstraint(preference_constraint, ("day", "start"))

# Solve
solution = problem.getSolution()

if not solution:
    raise RuntimeError("No feasible meeting time found with the given constraints.")

day = solution["day"]
start = solution["start"]
end = add_minutes(start, 30)

# Outputs must include both the time range in braces and the day of the week.
print(f"{day} {{{start}:{end}}}")
# Also output the plain HH:MM:HH:MM format as requested.
print(f"{start}:{end}")