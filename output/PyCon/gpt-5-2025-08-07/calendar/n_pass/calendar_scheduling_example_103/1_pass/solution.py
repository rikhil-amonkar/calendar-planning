# Requires: python-constraint
# If not installed, run: pip install python-constraint

from constraint import Problem

def minutes(h, m):
    return h * 60 + m

def fmt(mm):
    h = mm // 60
    m = mm % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Meeting parameters
    day_of_week = "Monday"
    work_start = minutes(9, 0)
    work_end = minutes(17, 0)
    duration = 30  # minutes

    # Participants' blocked times on Monday (start inclusive, end exclusive)
    blocked = {
        "Diane": [
            (minutes(9, 30), minutes(10, 0)),
            (minutes(14, 30), minutes(15, 0)),
        ],
        "Jack": [
            (minutes(13, 30), minutes(14, 0)),
            (minutes(14, 30), minutes(15, 0)),
        ],
        "Eugene": [
            (minutes(9, 0), minutes(10, 0)),
            (minutes(10, 30), minutes(11, 30)),
            (minutes(12, 0), minutes(14, 30)),
            (minutes(15, 0), minutes(16, 30)),
        ],
        "Patricia": [
            (minutes(9, 30), minutes(10, 30)),
            (minutes(11, 0), minutes(12, 0)),
            (minutes(12, 30), minutes(14, 0)),
            (minutes(15, 0), minutes(16, 30)),
        ],
    }

    # Build constraint problem
    problem = Problem()

    # Possible start times on 30-minute grid within work hours ensuring meeting fits entirely
    domain = list(range(work_start, work_end - duration + 1, 30))
    problem.addVariable("start", domain)

    # Constraint: no overlap with any participant's blocked times
    def no_overlap(s):
        e = s + duration
        # Ensure within work hours (redundant due to domain but kept for safety)
        if s < work_start or e > work_end:
            return False
        for person, slots in blocked.items():
            for bs, be in slots:
                if s < be and e > bs:  # overlap condition
                    return False
        return True

    problem.addConstraint(no_overlap, ["start"])

    solution = problem.getSolution()
    if not solution:
        raise SystemExit("No feasible meeting time found.")

    s = solution["start"]
    e = s + duration
    time_range = f"{fmt(s)}:{fmt(e)}"

    # Output requirements:
    # - time range in braces, like {14:30:15:30}
    # - day of the week on a separate line
    print(f"{{{time_range}}}")
    print(day_of_week)

if __name__ == "__main__":
    main()