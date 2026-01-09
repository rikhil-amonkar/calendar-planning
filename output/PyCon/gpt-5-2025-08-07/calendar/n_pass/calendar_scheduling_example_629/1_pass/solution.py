# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

# Meeting parameters
DURATION = 30  # minutes
WORK_START = 9 * 60
WORK_END = 17 * 60

# Days under consideration
DAYS = ["Monday", "Tuesday"]

# Blocked times in minutes from midnight
blocked = {
    "Monday": {
        "Margaret": [
            (10 * 60 + 30, 11 * 60),
            (11 * 60 + 30, 12 * 60),
            (13 * 60, 13 * 60 + 30),
            (15 * 60, 17 * 60),
        ],
        "Alexis": [
            (9 * 60 + 30, 11 * 60 + 30),
            (12 * 60 + 30, 13 * 60),
            (14 * 60, 17 * 60),
        ],
    },
    "Tuesday": {
        "Margaret": [
            (12 * 60, 12 * 60 + 30),
        ],
        "Alexis": [
            (9 * 60, 9 * 60 + 30),
            (10 * 60, 10 * 60 + 30),
            (14 * 60, 16 * 60 + 30),
        ],
    },
}

def minutes_range(start, end, step):
    return list(range(start, end, step))

def overlaps(a_start, a_end, b_start, b_end):
    # half-open intervals [start, end)
    return a_start < b_end and a_end > b_start

def availability_constraint(day, start):
    end = start + DURATION
    # Within work hours
    if not (WORK_START <= start and end <= WORK_END):
        return False
    # No overlaps with any participant's blocked times
    for intervals in blocked.get(day, {}).values():
        for s, e in intervals:
            if overlaps(start, end, s, e):
                return False
    return True

def preference_constraint(day, start):
    # Margaret does not want to meet on Monday
    if day == "Monday":
        return False
    # On Tuesday, not before 14:30
    if day == "Tuesday" and start < (14 * 60 + 30):
        return False
    return True

def mm_to_hhmm(m):
    h = m // 60
    mn = m % 60
    return f"{h:02d}:{mn:02d}"

def main():
    problem = Problem()
    # Start times at 30-minute granularity within working hours
    start_times = minutes_range(WORK_START, WORK_END, 30)  # last possible start is 16:30

    problem.addVariable("day", DAYS)
    problem.addVariable("start", start_times)

    problem.addConstraint(availability_constraint, ["day", "start"])
    problem.addConstraint(preference_constraint, ["day", "start"])

    solutions = problem.getSolutions()
    if not solutions:
        print("No feasible meeting time found.")
        return

    # Choose the earliest valid time based on day order and start time
    day_index = {d: i for i, d in enumerate(DAYS)}
    best = min(solutions, key=lambda s: (day_index[s["day"]], s["start"]))

    start = best["start"]
    end = start + DURATION
    day = best["day"]

    start_str = mm_to_hhmm(start)
    end_str = mm_to_hhmm(end)

    # Output day and time range in requested format
    print(day)
    print(f"{{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()