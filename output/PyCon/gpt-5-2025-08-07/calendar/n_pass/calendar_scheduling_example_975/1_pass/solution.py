from constraint import Problem

# Helper functions
def to_min(tstr):
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

def to_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Constants
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
work_start = to_min("09:00")
work_end = to_min("17:00")
duration = 60  # minutes
slot_step = 30  # minutes

# Schedules (busy intervals) per participant
schedules = {
    "Nicole": {
        "Tuesday": [(to_min("16:00"), to_min("16:30"))],
        "Wednesday": [(to_min("15:00"), to_min("15:30"))],
        "Friday": [(to_min("12:00"), to_min("12:30")), (to_min("15:30"), to_min("16:00"))],
    },
    "Daniel": {
        "Monday": [(to_min("09:00"), to_min("12:30")),
                   (to_min("13:00"), to_min("13:30")),
                   (to_min("14:00"), to_min("16:30"))],
        "Tuesday": [(to_min("09:00"), to_min("10:30")),
                    (to_min("11:30"), to_min("12:30")),
                    (to_min("13:00"), to_min("13:30")),
                    (to_min("15:00"), to_min("16:00")),
                    (to_min("16:30"), to_min("17:00"))],
        "Wednesday": [(to_min("09:00"), to_min("10:00")),
                      (to_min("11:00"), to_min("12:30")),
                      (to_min("13:00"), to_min("13:30")),
                      (to_min("14:00"), to_min("14:30")),
                      (to_min("16:30"), to_min("17:00"))],
        "Thursday": [(to_min("11:00"), to_min("12:00")),
                     (to_min("13:00"), to_min("14:00")),
                     (to_min("15:00"), to_min("15:30"))],
        "Friday": [(to_min("10:00"), to_min("11:00")),
                   (to_min("11:30"), to_min("12:00")),
                   (to_min("12:30"), to_min("14:30")),
                   (to_min("15:00"), to_min("15:30")),
                   (to_min("16:00"), to_min("16:30"))],
    }
}

# Build constraint problem
problem = Problem()
problem.addVariable("day", days)
start_domain = list(range(work_start, work_end - duration + 1, slot_step))
problem.addVariable("start", start_domain)

def no_overlap(day, start):
    end = start + duration
    # Ensure within work hours
    if start < work_start or end > work_end:
        return False
    # Check against all participants' busy slots for the chosen day
    for person, cal in schedules.items():
        for (s, e) in cal.get(day, []):
            # Overlap if start < e and end > s
            if start < e and end > s:
                return False
    return True

problem.addConstraint(no_overlap, ("day", "start"))

solutions = problem.getSolutions()

# Select earliest by day order then start time
if not solutions:
    raise RuntimeError("No feasible meeting time found, but problem statement guarantees a solution.")

day_index = {d: i for i, d in enumerate(days)}
best = sorted(solutions, key=lambda sol: (day_index[sol["day"]], sol["start"]))[0]

start = best["start"]
end = start + duration
day = best["day"]

# Output includes both time range and day
print(f"{day} {{{to_str(start)}:{to_str(end)}}}")