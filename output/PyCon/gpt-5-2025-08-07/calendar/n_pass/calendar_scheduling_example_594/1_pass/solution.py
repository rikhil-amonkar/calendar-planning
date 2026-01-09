# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def from_minutes(total):
    h = total // 60
    m = total % 60
    return f"{h:02d}:{m:02d}"

def overlaps(a_start, a_end, b_start, b_end):
    # Half-open intervals [start, end); overlap if a_start < b_end and b_start < a_end
    return a_start < b_end and b_start < a_end

def is_free(start, duration, busy_blocks):
    end = start + duration
    for (bs, be) in busy_blocks:
        if overlaps(start, end, bs, be):
            return False
    return True

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 30  # minutes

    # Busy schedules (inclusive start, exclusive end convention)
    adam_busy = [
        (to_minutes("09:30"), to_minutes("10:00")),
        (to_minutes("12:30"), to_minutes("13:00")),
        (to_minutes("14:30"), to_minutes("15:00")),
        (to_minutes("16:30"), to_minutes("17:00")),
    ]
    roy_busy = [
        (to_minutes("10:00"), to_minutes("11:00")),
        (to_minutes("11:30"), to_minutes("13:00")),
        (to_minutes("13:30"), to_minutes("14:30")),
        (to_minutes("16:30"), to_minutes("17:00")),
    ]

    all_busy = adam_busy + roy_busy

    # Candidate start times every 30 minutes within work window
    starts = list(range(work_start, work_end - duration + 1, 30))

    problem = Problem()
    problem.addVariable("start", starts)

    # Constraint: selected slot must be free for all participants
    def feasibility_constraint(start):
        return is_free(start, duration, all_busy)

    problem.addConstraint(feasibility_constraint, ("start",))

    # Find all feasible starts and pick the earliest (preference: earliest availability)
    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No feasible meeting time found.")

    earliest = min(solutions, key=lambda s: s["start"])
    start_min = earliest["start"]
    end_min = start_min + duration

    start_str = from_minutes(start_min)
    end_str = from_minutes(end_min)

    # Outputs:
    # 1) Exact time range format HH:MM:HH:MM
    # 2) Day of the week
    # 3) Time range in braces plus day (as explicitly required)
    print(f"{start_str}:{end_str}")
    print(day)
    print(f"{{{start_str}:{end_str}}} {day}")

if __name__ == "__main__":
    main()