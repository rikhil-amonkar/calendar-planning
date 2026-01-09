# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

def m(h, mm):
    return h * 60 + mm

def overlaps(a_start, a_end, b_start, b_end):
    return max(a_start, b_start) < min(a_end, b_end)

def is_free(busy_map, day, start, end):
    for bs, be in busy_map[day]:
        if overlaps(start, end, bs, be):
            return False
    return True

def fmt_time(minutes):
    h = minutes // 60
    mm = minutes % 60
    return f"{h:02d}:{mm:02d}"

if __name__ == "__main__":
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

    natalie = {
        "Monday":    [(m(9,0), m(9,30)), (m(10,0), m(12,0)), (m(12,30), m(13,0)), (m(14,0), m(14,30)), (m(15,0), m(16,30))],
        "Tuesday":   [(m(9,0), m(9,30)), (m(10,0), m(10,30)), (m(12,30), m(14,0)), (m(16,0), m(17,0))],
        "Wednesday": [(m(11,0), m(11,30)), (m(16,0), m(16,30))],
        "Thursday":  [(m(10,0), m(11,0)), (m(11,30), m(15,0)), (m(15,30), m(16,0)), (m(16,30), m(17,0))],
    }

    william = {
        "Monday":    [(m(9,30), m(11,0)), (m(11,30), m(17,0))],
        "Tuesday":   [(m(9,0), m(13,0)), (m(13,30), m(16,0))],
        "Wednesday": [(m(9,0), m(12,30)), (m(13,0), m(14,30)), (m(15,30), m(16,0)), (m(16,30), m(17,0))],
        "Thursday":  [(m(9,0), m(10,30)), (m(11,0), m(11,30)), (m(12,0), m(12,30)), (m(13,0), m(14,0)), (m(15,0), m(17,0))],
    }

    work_start = m(9, 0)
    work_end = m(17, 0)
    duration = 60  # minutes

    # Build domain: all (day_index, start_time) with 30-minute granularity within work hours
    domain = []
    for di, d in enumerate(days):
        start = work_start
        while start + duration <= work_end:
            domain.append((di, start))
            start += 30  # 30-minute increments

    problem = Problem()
    problem.addVariable("slot", domain)

    def availability_constraint(slot):
        di, start = slot
        end = start + duration
        day = days[di]
        return is_free(natalie, day, start, end) and is_free(william, day, start, end)

    problem.addConstraint(availability_constraint, ["slot"])

    solutions = problem.getSolutions()

    if not solutions:
        print("No feasible meeting time found.")
    else:
        # Choose the earliest by day then start time for determinism
        best = min(solutions, key=lambda s: (s["slot"][0], s["slot"][1]))
        di, start = best["slot"]
        end = start + duration
        day_name = days[di]
        start_str = fmt_time(start)
        end_str = fmt_time(end)
        # Output includes both day and time in {HH:MM:HH:MM}
        print(f"{day_name} {{{start_str}:{end_str}}}")