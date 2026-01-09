# Requires: python-constraint
# This script finds a 30-minute meeting time on Monday between 09:00 and 17:00
# that works for all participants given their busy schedules. It outputs the day
# and the selected time in the format {HH:MM:HH:MM}.

from constraint import Problem

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def to_hhmm(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def no_overlap_constraint(busy_intervals, duration):
    def constraint(start_time):
        end_time = start_time + duration
        # No overlap if [start, end) does not intersect any [s, e)
        for s, e in busy_intervals:
            if not (end_time <= s or start_time >= e):
                return False
        return True
    return constraint

def main():
    day = "Monday"
    duration = 30  # minutes
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")

    # Define busy schedules (inclusive of start, exclusive of end)
    busy = {
        "Gregory":   [(to_minutes("09:00"), to_minutes("09:30")),
                      (to_minutes("11:30"), to_minutes("12:00"))],
        "Jonathan":  [(to_minutes("09:00"), to_minutes("09:30")),
                      (to_minutes("12:00"), to_minutes("12:30")),
                      (to_minutes("13:00"), to_minutes("13:30")),
                      (to_minutes("15:00"), to_minutes("16:00")),
                      (to_minutes("16:30"), to_minutes("17:00"))],
        "Barbara":   [(to_minutes("10:00"), to_minutes("10:30")),
                      (to_minutes("13:30"), to_minutes("14:00"))],
        "Jesse":     [(to_minutes("10:00"), to_minutes("11:00")),
                      (to_minutes("12:30"), to_minutes("14:30"))],
        "Alan":      [(to_minutes("09:30"), to_minutes("11:00")),
                      (to_minutes("11:30"), to_minutes("12:30")),
                      (to_minutes("13:00"), to_minutes("15:30")),
                      (to_minutes("16:00"), to_minutes("17:00"))],
        "Nicole":    [(to_minutes("09:00"), to_minutes("10:30")),
                      (to_minutes("11:30"), to_minutes("12:00")),
                      (to_minutes("12:30"), to_minutes("13:30")),
                      (to_minutes("14:00"), to_minutes("17:00"))],
        "Catherine": [(to_minutes("09:00"), to_minutes("10:30")),
                      (to_minutes("12:00"), to_minutes("13:30")),
                      (to_minutes("15:00"), to_minutes("15:30")),
                      (to_minutes("16:00"), to_minutes("16:30"))],
    }

    # Candidate start times in 30-minute increments within work hours
    candidates = list(range(work_start, work_end - duration + 1, 30))

    problem = Problem()
    problem.addVariable("start", candidates)

    # Add one constraint per participant to ensure no overlap
    for intervals in busy.values():
        problem.addConstraint(no_overlap_constraint(intervals, duration), ["start"])

    # Solve and pick the earliest valid time
    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No feasible meeting time found.")
    best = min(solutions, key=lambda s: s["start"])
    start = best["start"]
    end = start + duration

    # Output: day and time range in {HH:MM:HH:MM}
    print(day)
    print(f"{{{to_hhmm(start)}:{to_hhmm(end)}}}")

if __name__ == "__main__":
    main()