# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

def parse_time(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def overlaps(start, duration, intervals):
    end = start + duration
    for s, e in intervals:
        if start < e and end > s:
            return True
    return False

def main():
    day = "Monday"
    duration = 30  # minutes
    step = 30

    work_start = parse_time("09:00")
    work_end = parse_time("17:00")

    # Busy schedules (inclusive of start, exclusive of end)
    schedules = {
        "Raymond": [("09:00","09:30"), ("11:30","12:00"), ("13:00","13:30"), ("15:00","15:30")],
        "Billy":   [("10:00","10:30"), ("12:00","13:00"), ("16:30","17:00")],
        "Donald":  [("09:00","09:30"), ("10:00","11:00"), ("12:00","13:00"), ("14:00","14:30"), ("16:00","17:00")],
    }

    # Convert to minutes
    busy_minutes = {}
    for person, intervals in schedules.items():
        busy_minutes[person] = [(parse_time(s), parse_time(e)) for s, e in intervals]

    # Domain of possible start times (every 30 minutes within work hours)
    domain = list(range(work_start, work_end - duration + 1, step))

    problem = Problem()
    problem.addVariable("start", domain)

    # Constraint: start must not overlap with any participant's busy intervals
    def all_available(start):
        for person in busy_minutes:
            if overlaps(start, duration, busy_minutes[person]):
                return False
        return True

    problem.addConstraint(all_available, ["start"])

    solutions = problem.getSolutions()

    # Preference: Billy would like to avoid meetings after 15:00 (i.e., meeting ends by 15:00)
    prefer_end_by = parse_time("15:00")
    preferred = [sol for sol in solutions if sol["start"] + duration <= prefer_end_by]

    chosen = None
    if preferred:
        chosen = min(preferred, key=lambda s: s["start"])
    elif solutions:
        chosen = min(solutions, key=lambda s: s["start"])

    if not chosen:
        raise RuntimeError("No feasible meeting time found, but a solution was expected.")

    start = chosen["start"]
    end = start + duration
    time_range = f"{fmt_time(start)}:{fmt_time(end)}"

    # Output must include both the time range and the day of the week.
    # Example format: "Monday {14:30:15:30}"
    print(f"{day} {{{time_range}}}")

if __name__ == "__main__":
    main()