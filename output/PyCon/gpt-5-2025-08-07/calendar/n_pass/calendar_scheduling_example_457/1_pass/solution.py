# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

def time_to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def min_to_time(m):
    return f"{m//60:02d}:{m%60:02d}"

def overlaps(a_start, a_end, b_start, b_end):
    return not (a_end <= b_start or a_start >= b_end)

def make_busy_intervals(pairs):
    return [(time_to_min(s), time_to_min(e)) for s, e in pairs]

def main():
    # Meeting details
    day = "Monday"
    meeting_duration = 30  # minutes
    work_start = time_to_min("09:00")
    work_end = time_to_min("17:00")

    # Participants' busy schedules (Monday)
    busy = {
        "Andrea": make_busy_intervals([("09:30", "10:30"), ("13:30", "14:30")]),
        "Ruth": make_busy_intervals([("12:30", "13:00"), ("15:00", "15:30")]),
        "Steven": make_busy_intervals([("10:00", "10:30"), ("11:00", "11:30"),
                                       ("12:00", "12:30"), ("13:30", "14:00"),
                                       ("15:00", "16:00")]),
        "Grace": make_busy_intervals([]),
        "Kyle": make_busy_intervals([("09:00", "09:30"), ("10:30", "12:00"),
                                     ("12:30", "13:00"), ("13:30", "15:00"),
                                     ("15:30", "16:00"), ("16:30", "17:00")]),
        "Elijah": make_busy_intervals([("09:00", "11:00"), ("11:30", "13:00"),
                                       ("13:30", "14:00"), ("15:30", "16:00"),
                                       ("16:30", "17:00")]),
        "Lori": make_busy_intervals([("09:00", "09:30"), ("10:00", "11:30"),
                                     ("12:00", "13:30"), ("14:00", "16:00"),
                                     ("16:30", "17:00")]),
    }

    # Set up constraint problem
    problem = Problem()
    # Possible 30-min start times within work hours
    starts = list(range(work_start, work_end - meeting_duration + 1, 30))
    problem.addVariable("start", starts)
    problem.addVariable("day", [day])

    # For each participant, ensure the meeting does not overlap with their busy times
    for person, intervals in busy.items():
        def availability_constraint(s, ivs=intervals):
            end = s + meeting_duration
            for b_start, b_end in ivs:
                if overlaps(s, end, b_start, b_end):
                    return False
            return True
        problem.addConstraint(availability_constraint, ["start"])

    # Solve and pick the earliest feasible start
    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No feasible meeting time found.")

    best = min(solutions, key=lambda sol: sol["start"])
    start_min = best["start"]
    end_min = start_min + meeting_duration

    start_str = min_to_time(start_min)
    end_str = min_to_time(end_min)

    # Output must include both the time range in {HH:MM:HH:MM} and the day of week
    print(f"{best['day']} {{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()