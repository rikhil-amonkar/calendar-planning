# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m//60:02d}:{m%60:02d}"

def overlaps(start, duration, blocks):
    end = start + duration
    for bs, be in blocks:
        if start < be and end > bs:
            return True
    return False

def main():
    day = "Monday"
    meeting_duration = 30  # minutes
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")

    # Busy schedules (inclusive start, exclusive end)
    busy_raw = {
        "Steven": [],
        "Roy": [],
        "Cynthia": [("09:30","10:30"), ("11:30","12:00"), ("13:00","13:30"), ("15:00","16:00")],
        "Lauren":  [("09:00","09:30"), ("10:30","11:00"), ("11:30","12:00"), ("13:00","13:30"),
                    ("14:00","14:30"), ("15:00","15:30"), ("16:00","17:00")],
        "Robert":  [("10:30","11:00"), ("11:30","12:00"), ("12:30","13:30"), ("14:00","16:00")],
    }

    busy = {p: [(to_minutes(s), to_minutes(e)) for s, e in slots] for p, slots in busy_raw.items()}

    # Candidate start times in 30-minute increments within working hours
    domain = list(range(work_start, work_end - meeting_duration + 1, 30))

    problem = Problem()
    problem.addVariable("start", domain)

    # Add constraints for each participant to ensure the 30-minute slot doesn't overlap their busy times
    for person, blocks in busy.items():
        problem.addConstraint(lambda s, blks=blocks: not overlaps(s, meeting_duration, blks), ("start",))

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No feasible meeting time found, but one was expected.")

    # Earliest feasible start
    earliest_start = min(sol["start"] for sol in solutions)
    start_str = to_hhmm(earliest_start)
    end_str = to_hhmm(earliest_start + meeting_duration)

    # Output includes time range in braces and the day of the week
    print(f"{{{start_str}:{end_str}}} {day}")

if __name__ == "__main__":
    main()