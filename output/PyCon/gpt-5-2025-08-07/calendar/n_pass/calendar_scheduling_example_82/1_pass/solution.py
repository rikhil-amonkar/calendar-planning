# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def to_hhmm(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def no_overlap_with(blocked_intervals, duration):
    def constraint(start):
        s, e = start, start + duration
        for bs, be in blocked_intervals:
            # Overlap if not (end <= bs or start >= be)
            if not (e <= bs or s >= be):
                return False
        return True
    return constraint

def main():
    day = "Monday"
    meeting_duration = 30  # minutes
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")

    # Participants' blocked intervals on Monday
    michael_blocked = [
        (to_minutes("09:30"), to_minutes("10:30")),
        (to_minutes("15:00"), to_minutes("15:30")),
        (to_minutes("16:00"), to_minutes("16:30")),
    ]
    eric_blocked = []  # Eric is free all day
    arthur_blocked = [
        (to_minutes("09:00"), to_minutes("12:00")),
        (to_minutes("13:00"), to_minutes("15:00")),
        (to_minutes("15:30"), to_minutes("16:00")),
        (to_minutes("16:30"), to_minutes("17:00")),
    ]

    # Domain: all possible 30-minute start times within work hours
    # Start times such that start + duration <= work_end
    domain = list(range(work_start, work_end - meeting_duration + 1, 30))

    problem = Problem()
    problem.addVariable("start", domain)

    # Constraints: no overlaps with any participant's blocked intervals
    problem.addConstraint(no_overlap_with(michael_blocked, meeting_duration), ["start"])
    problem.addConstraint(no_overlap_with(eric_blocked, meeting_duration), ["start"])
    problem.addConstraint(no_overlap_with(arthur_blocked, meeting_duration), ["start"])

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No feasible meeting time found, but a solution was expected.")

    # Choose the earliest feasible start time
    best = min(solutions, key=lambda sol: sol["start"])
    start = best["start"]
    end = start + meeting_duration

    start_str = to_hhmm(start)
    end_str = to_hhmm(end)

    # Output must include both the time range in {HH:MM:HH:MM} and the day of the week
    print(f"{{{start_str}:{end_str}}}")
    print(day)

if __name__ == "__main__":
    main()