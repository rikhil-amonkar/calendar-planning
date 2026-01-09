# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

def parse_time(tstr):
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Configuration
days = ["Monday", "Tuesday", "Wednesday"]
day_index = {name: i for i, name in enumerate(days)}
work_start = parse_time("09:00")
work_end = parse_time("17:00")
duration = 30  # minutes

# Blocked schedules (inclusive of start, exclusive of end)
# Provide intervals as tuples (start_minute, end_minute)
def intervals(*pairs):
    return [(parse_time(a), parse_time(b)) for a, b in pairs]

blocked = {
    "Ronald": {
        day_index["Monday"]: intervals(("10:30","11:00"), ("12:00","12:30"), ("15:30","16:00")),
        day_index["Tuesday"]: intervals(("09:00","09:30"), ("12:00","12:30"), ("15:30","16:30")),
        day_index["Wednesday"]: intervals(("09:30","10:30"), ("11:00","12:00"), ("12:30","13:00"),
                                          ("13:30","14:00"), ("16:30","17:00")),
    },
    "Amber": {
        day_index["Monday"]: intervals(("09:00","09:30"), ("10:00","10:30"), ("11:30","12:00"),
                                       ("12:30","14:00"), ("14:30","15:00"), ("15:30","17:00")),
        day_index["Tuesday"]: intervals(("09:00","09:30"), ("10:00","11:30"), ("12:00","12:30"),
                                        ("13:30","15:30"), ("16:30","17:00")),
        day_index["Wednesday"]: intervals(("09:00","09:30"), ("10:00","10:30"), ("11:00","13:30"),
                                          ("15:00","15:30")),
    },
}

# Build candidate start times in 30-minute increments within work hours
candidate_starts = list(range(work_start, work_end - duration + 1, 30))

problem = Problem()
problem.addVariable("day", list(range(len(days))))
problem.addVariable("start", candidate_starts)

def within_work_hours(d, s):
    return work_start <= s and s + duration <= work_end

def no_overlap_for_all(d, s):
    e = s + duration
    for person, sched in blocked.items():
        for (bs, be) in sched.get(d, []):
            # Overlap if not (meeting ends before block starts OR meeting starts after block ends)
            if not (e <= bs or s >= be):
                return False
    return True

problem.addConstraint(within_work_hours, ("day", "start"))
problem.addConstraint(no_overlap_for_all, ("day", "start"))

solutions = problem.getSolutions()
if not solutions:
    # Per instructions, a solution exists; this is a safety net.
    print("No feasible meeting time found.")
else:
    # Earliest availability: sort by day then start time
    best = min(solutions, key=lambda x: (x["day"], x["start"]))
    day_name = days[best["day"]]
    start_min = best["start"]
    end_min = start_min + duration
    start_str = fmt_time(start_min)
    end_str = fmt_time(end_min)
    # Output day and time range in required formats
    print(day_name)
    print(f"{{{start_str}:{end_str}}}")