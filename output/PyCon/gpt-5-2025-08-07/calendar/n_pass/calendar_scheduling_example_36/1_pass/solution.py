# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def from_minutes(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def no_overlap(start, duration, busy_intervals):
    end = start + duration
    for bs, be in busy_intervals:
        # Overlap if intervals intersect
        if start < be and end > bs:
            return False
    return True

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 60  # 1 hour meeting

    # Existing schedules (busy intervals) on Monday
    ryan_busy = [
        (to_minutes("09:00"), to_minutes("09:30")),
        (to_minutes("12:30"), to_minutes("13:00")),
    ]
    ruth_busy = []  # no meetings
    denise_busy = [
        (to_minutes("09:30"), to_minutes("10:30")),
        (to_minutes("12:00"), to_minutes("13:00")),
        (to_minutes("14:30"), to_minutes("16:30")),
    ]

    # Denise does not want to meet after 12:30 (meeting must end by 12:30)
    denise_latest_end = to_minutes("12:30")

    # Candidate start times in 30-minute increments within working hours
    candidate_starts = list(range(work_start, work_end - duration + 1, 30))

    problem = Problem()
    problem.addVariable("start", candidate_starts)

    # Constraints: avoid overlaps with each participant's busy times
    problem.addConstraint(lambda s: no_overlap(s, duration, ryan_busy), ["start"])
    problem.addConstraint(lambda s: no_overlap(s, duration, ruth_busy), ["start"])
    problem.addConstraint(lambda s: no_overlap(s, duration, denise_busy), ["start"])

    # Denise preference: meeting must end by 12:30
    problem.addConstraint(lambda s: s + duration <= denise_latest_end, ["start"])

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No feasible meeting time found.")

    # Choose the earliest feasible start time
    best = min(solutions, key=lambda sol: sol["start"])
    start = best["start"]
    end = start + duration

    time_range = f"{from_minutes(start)}:{from_minutes(end)}"
    print(f"{day} {{{time_range}}}")

if __name__ == "__main__":
    main()