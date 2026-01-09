from constraint import Problem

def minutes(h, m):
    return h * 60 + m

def fmt(mm):
    return f"{mm // 60:02d}:{mm % 60:02d}"

def make_no_overlap_constraint(busy_intervals, duration):
    def constraint(start):
        end = start + duration
        for s, e in busy_intervals:
            # Overlap if not (meeting ends before busy starts) or (busy ends before meeting starts)
            if not (end <= s or e <= start):
                return False
        return True
    return constraint

def main():
    day = "Monday"
    work_start = minutes(9, 0)
    work_end = minutes(17, 0)
    duration = 30  # minutes

    # Busy schedules (start, end) in minutes since midnight
    schedules = {
        "Walter": [],  # no meetings
        "Cynthia": [
            (minutes(9, 0), minutes(9, 30)),
            (minutes(10, 0), minutes(10, 30)),
            (minutes(13, 30), minutes(14, 30)),
            (minutes(15, 0), minutes(16, 0)),
        ],
        "Ann": [
            (minutes(10, 0), minutes(11, 0)),
            (minutes(13, 0), minutes(13, 30)),
            (minutes(14, 0), minutes(15, 0)),
            (minutes(16, 0), minutes(16, 30)),
        ],
        "Catherine": [
            (minutes(9, 0), minutes(11, 30)),
            (minutes(12, 30), minutes(13, 30)),
            (minutes(14, 30), minutes(17, 0)),
        ],
        "Kyle": [
            (minutes(9, 0), minutes(9, 30)),
            (minutes(10, 0), minutes(11, 30)),
            (minutes(12, 0), minutes(12, 30)),
            (minutes(13, 0), minutes(14, 30)),
            (minutes(15, 0), minutes(16, 0)),
        ],
    }

    # Build domain of possible start times at 30-minute granularity
    domain = list(range(work_start, work_end - duration + 1, 30))

    problem = Problem()
    problem.addVariable("start", domain)

    # Add a no-overlap constraint for each participant
    for person, busy in schedules.items():
        problem.addConstraint(make_no_overlap_constraint(busy, duration), ["start"])

    solutions = problem.getSolutions()
    if not solutions:
        print("No feasible meeting time found.")
        return

    # Choose the earliest feasible start time
    best_start = min(sol["start"] for sol in solutions)
    best_end = best_start + duration

    # Output in the required format
    print(f"{{{fmt(best_start)}:{fmt(best_end)}}}")
    print(day)

if __name__ == "__main__":
    main()