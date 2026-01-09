# Requires: python-constraint
from constraint import Problem

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def format_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

def no_overlap_factory(busy_intervals, duration):
    def constraint(start):
        end = start + duration
        for (bs, be) in busy_intervals:
            # Overlap if intervals intersect: not (end <= bs or start >= be)
            if not (end <= bs or start >= be):
                return False
        return True
    return constraint

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 60  # minutes

    # Domain: 30-minute increments so meeting ends by 17:00
    domain = list(range(work_start, work_end - duration + 1, 30))

    # Busy calendars (in minutes since midnight)
    calendars = {
        "Evelyn": [],
        "Joshua": [(to_minutes("11:00"), to_minutes("12:30")),
                   (to_minutes("13:30"), to_minutes("14:30")),
                   (to_minutes("16:30"), to_minutes("17:00"))],
        "Kevin": [],
        "Gerald": [],
        "Jerry": [(to_minutes("09:00"), to_minutes("09:30")),
                  (to_minutes("10:30"), to_minutes("12:00")),
                  (to_minutes("12:30"), to_minutes("13:00")),
                  (to_minutes("13:30"), to_minutes("14:00")),
                  (to_minutes("14:30"), to_minutes("15:00")),
                  (to_minutes("15:30"), to_minutes("16:00"))],
        "Jesse": [(to_minutes("09:00"), to_minutes("09:30")),
                  (to_minutes("10:30"), to_minutes("12:00")),
                  (to_minutes("12:30"), to_minutes("13:00")),
                  (to_minutes("14:30"), to_minutes("15:00")),
                  (to_minutes("15:30"), to_minutes("16:30"))],
        "Kenneth": [(to_minutes("10:30"), to_minutes("12:30")),
                    (to_minutes("13:30"), to_minutes("14:00")),
                    (to_minutes("14:30"), to_minutes("15:00")),
                    (to_minutes("15:30"), to_minutes("16:00")),
                    (to_minutes("16:30"), to_minutes("17:00"))],
    }

    problem = Problem()
    problem.addVariable("start", domain)

    # Add availability constraints for each participant
    for participant, busy in calendars.items():
        problem.addConstraint(no_overlap_factory(busy, duration), ["start"])

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No feasible meeting time found.")

    # Choose the earliest feasible start time
    best_start = min(sol["start"] for sol in solutions)
    start_str = format_time(best_start)
    end_str = format_time(best_start + duration)

    # Output the time range and the day of the week
    print(f"{{{start_str}:{end_str}}}")
    print(day)

if __name__ == "__main__":
    main()