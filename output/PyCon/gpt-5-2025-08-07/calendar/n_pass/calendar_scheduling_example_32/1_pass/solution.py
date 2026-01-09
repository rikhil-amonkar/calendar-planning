# Requires: python-constraint
from constraint import Problem

def t(h, m):
    return h * 60 + m

def fmt(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def overlaps(a_start, a_end, b_start, b_end):
    return a_start < b_end and a_end > b_start

def slot_free(slot, busy_intervals):
    s, e = slot
    for b_start, b_end in busy_intervals:
        if overlaps(s, e, b_start, b_end):
            return False
    return True

def main():
    day = "Monday"
    work_start = t(9, 0)
    work_end = t(17, 0)
    duration = 30  # minutes

    # Busy schedules (Monday)
    emily_busy = [
        (t(10, 0), t(10, 30)),
        (t(11, 30), t(12, 30)),
        (t(14, 0), t(15, 0)),
        (t(16, 0), t(16, 30)),
    ]
    melissa_busy = [
        (t(9, 30), t(10, 0)),
        (t(14, 30), t(15, 0)),
    ]
    frank_busy = [
        (t(10, 0), t(10, 30)),
        (t(11, 0), t(11, 30)),
        (t(12, 30), t(13, 0)),
        (t(13, 30), t(14, 30)),
        (t(15, 0), t(16, 0)),
        (t(16, 30), t(17, 0)),
    ]

    # Generate all 30-minute slots within work hours
    candidate_slots = []
    start = work_start
    while start + duration <= work_end:
        candidate_slots.append((start, start + duration))
        start += duration

    problem = Problem()
    problem.addVariable("slot", candidate_slots)

    # No overlap with participants' busy times
    problem.addConstraint(lambda slot: slot_free(slot, emily_busy), ["slot"])
    problem.addConstraint(lambda slot: slot_free(slot, melissa_busy), ["slot"])
    problem.addConstraint(lambda slot: slot_free(slot, frank_busy), ["slot"])

    # Preference: Frank does not want to meet on Monday after 09:30
    # Interpret as meeting must end by 09:30
    problem.addConstraint(lambda slot: slot[1] <= t(9, 30), ["slot"])

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No feasible meeting time found, but a solution was expected.")

    # Choose the earliest feasible slot
    chosen = min(solutions, key=lambda s: s["slot"][0])["slot"]
    start_str, end_str = fmt(chosen[0]), fmt(chosen[1])

    # Output must include both the time range like {HH:MM:HH:MM} and the day of the week
    print(f"{{{start_str}:{end_str}}}")
    print(day)

if __name__ == "__main__":
    main()