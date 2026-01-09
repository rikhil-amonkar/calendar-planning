# Requires: python-constraint (pip install python-constraint)
from constraint import Problem

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def overlaps(a_start, a_end, b_start, b_end):
    # Intervals are half-open [start, end); overlap if they intersect
    return not (a_end <= b_start or a_start >= b_end)

def build_allowed_starts(busy_intervals, domain_starts, duration):
    allowed = []
    for s in domain_starts:
        e = s + duration
        ok = True
        for (bs, be) in busy_intervals:
            if overlaps(s, e, bs, be):
                ok = False
                break
        if ok:
            allowed.append(s)
    return allowed

def main():
    day = "Monday"
    meeting_duration = 30  # minutes
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")

    # Domain of possible half-hour starts within work hours
    domain_starts = [t for t in range(work_start, work_end - meeting_duration + 1, 30)]

    # Busy schedules (inclusive of start, exclusive of end)
    schedules = {
        "Joan": [("11:30", "12:00"), ("14:30", "15:00")],
        "Megan": [("09:00", "10:00"), ("14:00", "14:30"), ("16:00", "16:30")],
        "Austin": [],  # free entire day
        "Betty": [("09:30", "10:00"), ("11:30", "12:00"), ("13:30", "14:00"), ("16:00", "16:30")],
        "Judith": [("09:00", "11:00"), ("12:00", "13:00"), ("14:00", "15:00")],
        "Terry": [("09:30", "10:00"), ("11:30", "12:30"), ("13:00", "14:00"), ("15:00", "15:30"), ("16:00", "17:00")],
        "Kathryn": [("09:30", "10:00"), ("10:30", "11:00"), ("11:30", "13:00"), ("14:00", "16:00"), ("16:30", "17:00")],
    }

    # Convert busy intervals to minutes
    busy_minutes = {
        person: [(to_minutes(s), to_minutes(e)) for (s, e) in intervals]
        for person, intervals in schedules.items()
    }

    # Set up constraint problem
    problem = Problem()
    problem.addVariable("start", domain_starts)

    # For each participant, constrain start to be in their allowed times
    for person, intervals in busy_minutes.items():
        allowed = build_allowed_starts(intervals, domain_starts, meeting_duration)
        problem.addConstraint(lambda s, A=tuple(allowed): s in A, ("start",))

    # Solve and pick the earliest valid start
    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No feasible meeting time found.")
    earliest = min(solutions, key=lambda sol: sol["start"])
    start = earliest["start"]
    end = start + meeting_duration

    # Output
    start_str = to_hhmm(start)
    end_str = to_hhmm(end)
    print(day)
    print(f"{{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()