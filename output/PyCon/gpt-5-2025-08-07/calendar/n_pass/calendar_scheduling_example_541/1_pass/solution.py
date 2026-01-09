from constraint import Problem

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m//60:02d}:{m%60:02d}"

def overlaps(a_start, a_end, b_start, b_end):
    return a_start < b_end and b_start < a_end

def main():
    # Meeting parameters
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 60  # minutes
    step = 30      # consider start times in 30-minute increments

    # Participants' blocked times on Monday
    schedules = {
        "Kayla": [("10:00", "10:30"), ("14:30", "16:00")],
        "Rebecca": [("09:00", "13:00"), ("13:30", "15:00"), ("15:30", "16:00")],
    }

    # Convert schedules to minute ranges
    blocked_intervals = []
    for person, intervals in schedules.items():
        for s, e in intervals:
            blocked_intervals.append((to_minutes(s), to_minutes(e)))

    # Build domain of possible start times within work hours
    domain_starts = [t for t in range(work_start, work_end - duration + 1, step)]

    # Setup constraint problem
    problem = Problem()
    problem.addVariable("start", domain_starts)
    problem.addVariable("day", [day])

    # Constraints: meeting must not overlap any blocked interval and end within work hours
    def availability_constraint(start, d):
        end = start + duration
        if end > work_end:
            return False
        for b_start, b_end in blocked_intervals:
            if overlaps(start, end, b_start, b_end):
                return False
        return True

    problem.addConstraint(availability_constraint, ("start", "day"))

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No feasible meeting time found.")

    # Choose earliest valid start time
    best = min(solutions, key=lambda s: s["start"])
    start = best["start"]
    end = start + duration

    # Output: must include both the time range (like {14:30:15:30}) and the day of the week
    time_range = f"{to_hhmm(start)}:{to_hhmm(end)}"
    print(f"{{{time_range}}}")
    print(best["day"])

if __name__ == "__main__":
    main()