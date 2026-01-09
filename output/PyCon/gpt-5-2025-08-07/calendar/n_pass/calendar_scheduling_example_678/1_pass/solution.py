from constraint import Problem

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt_time(minutes):
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

def overlaps(start1, end1, start2, end2):
    return start1 < end2 and start2 < end1

def is_free(day, start, duration, schedules):
    end = start + duration
    for (b_start, b_end) in schedules.get(day, []):
        if overlaps(start, end, b_start, b_end):
            return False
    return True

if __name__ == "__main__":
    # Work hours and meeting duration
    WORK_START = to_minutes("09:00")
    WORK_END = to_minutes("17:00")
    DURATION = 60  # minutes

    # Busy schedules (in minutes from 00:00)
    russell_busy = {
        "Monday": [(to_minutes("10:30"), to_minutes("11:00"))],
        "Tuesday": [(to_minutes("13:00"), to_minutes("13:30"))],
    }
    alexander_busy = {
        "Monday": [
            (to_minutes("09:00"), to_minutes("11:30")),
            (to_minutes("12:00"), to_minutes("14:30")),
            (to_minutes("15:00"), to_minutes("17:00")),
        ],
        "Tuesday": [
            (to_minutes("09:00"), to_minutes("10:00")),
            (to_minutes("13:00"), to_minutes("14:00")),
            (to_minutes("15:00"), to_minutes("15:30")),
            (to_minutes("16:00"), to_minutes("16:30")),
        ],
    }

    # Preference: Russell would rather not meet on Tuesday before 13:30 (treat as constraint)
    RUSSELL_TUE_EARLIEST = to_minutes("13:30")

    problem = Problem()
    days = ["Monday", "Tuesday"]
    # Start times in 5-minute increments
    starts = list(range(WORK_START, WORK_END - DURATION + 1, 5))

    problem.addVariable("day", days)
    problem.addVariable("start", starts)

    def constraint(day, start):
        end = start + DURATION
        # Within work hours
        if not (WORK_START <= start and end <= WORK_END):
            return False
        # Russell Tuesday preference
        if day == "Tuesday" and start < RUSSELL_TUE_EARLIEST:
            return False
        # Availability checks
        if not is_free(day, start, DURATION, russell_busy):
            return False
        if not is_free(day, start, DURATION, alexander_busy):
            return False
        return True

    problem.addConstraint(constraint, ("day", "start"))

    solutions = problem.getSolutions()

    if not solutions:
        # As per problem statement, a solution exists; this is just a fallback.
        raise SystemExit("No feasible meeting time found.")

    # Choose the earliest feasible by day then start time
    day_order = {"Monday": 0, "Tuesday": 1}
    best = min(solutions, key=lambda s: (day_order[s["day"]], s["start"]))

    day = best["day"]
    start = best["start"]
    end = start + DURATION

    # Output format requires both the time range in {HH:MM:HH:MM} and the day
    print(day)
    print(f"{{{fmt_time(start)}:{fmt_time(end)}}}")