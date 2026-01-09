# Requires: python-constraint
from constraint import Problem

def to_minutes(h, m):
    return h * 60 + m

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def overlaps(a_start, a_end, b_start, b_end):
    return not (a_end <= b_start or a_start >= b_end)

def main():
    # Meeting parameters
    day = "Monday"
    work_start = to_minutes(9, 0)
    work_end = to_minutes(17, 0)
    duration = 60  # 1 hour
    step = 30      # 30-minute increments

    # Busy schedules (inclusive start, exclusive end in minutes)
    julie_busy = [
        (to_minutes(9, 0),  to_minutes(9, 30)),
        (to_minutes(11, 0), to_minutes(11, 30)),
        (to_minutes(12, 0), to_minutes(12, 30)),
        (to_minutes(13, 30), to_minutes(14, 0)),
        (to_minutes(16, 0), to_minutes(17, 0)),
    ]
    sean_busy = [
        (to_minutes(9, 0),  to_minutes(9, 30)),
        (to_minutes(13, 0), to_minutes(13, 30)),
        (to_minutes(15, 0), to_minutes(15, 30)),
        (to_minutes(16, 0), to_minutes(16, 30)),
    ]
    lori_busy = [
        (to_minutes(10, 0), to_minutes(10, 30)),
        (to_minutes(11, 0), to_minutes(13, 0)),
        (to_minutes(15, 30), to_minutes(17, 0)),
    ]

    participants_busy = {
        "Julie": julie_busy,
        "Sean": sean_busy,
        "Lori": lori_busy,
    }

    # Candidate start times
    starts = list(range(work_start, work_end - duration + 1, step))

    # Constraint problem
    problem = Problem()
    problem.addVariable("start", starts)

    def no_conflicts(start):
        end = start + duration
        # Must be within working hours
        if start < work_start or end > work_end:
            return False
        # Check each participant's busy intervals
        for busy_list in participants_busy.values():
            for (b_start, b_end) in busy_list:
                if overlaps(start, end, b_start, b_end):
                    return False
        return True

    problem.addConstraint(no_conflicts, ["start"])

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No feasible meeting time found, but one was expected.")

    # Choose the earliest valid time
    best = min(solutions, key=lambda sol: sol["start"])
    start = best["start"]
    end = start + duration

    print(f"{{{format_time(start)}:{format_time(end)}}}")
    print(day)

if __name__ == "__main__":
    main()