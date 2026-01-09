# Requires: python-constraint
from constraint import Problem

MEETING_DURATION_MIN = 30

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def build_allowed_starts(work_start, work_end, duration, blocked_intervals):
    # Generate all 30-min start times within work hours that don't intersect blocked intervals
    starts = []
    t = work_start
    while t + duration <= work_end:
        end = t + duration
        # Check for overlap with any blocked interval
        overlaps = any(not (end <= b_start or t >= b_end) for (b_start, b_end) in blocked_intervals)
        if not overlaps:
            starts.append(t)
        t += 30
    return starts

def main():
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    dur = MEETING_DURATION_MIN

    # Jeffrey is free entire week -> no personal blocks beyond work hours

    # Harold's blocks
    harold_blocks = {
        "Monday": [
            (time_to_minutes("09:00"), time_to_minutes("10:00")),
            (time_to_minutes("10:30"), time_to_minutes("17:00")),
        ],
        "Tuesday": [
            (time_to_minutes("09:00"), time_to_minutes("09:30")),
            (time_to_minutes("10:30"), time_to_minutes("11:30")),
            (time_to_minutes("12:30"), time_to_minutes("13:30")),
            (time_to_minutes("14:30"), time_to_minutes("15:30")),
            (time_to_minutes("16:00"), time_to_minutes("17:00")),
        ],
    }

    # Build allowed starts per day considering Harold's blocks and work hours
    allowed_starts = {
        day: build_allowed_starts(work_start, work_end, dur, harold_blocks[day])
        for day in ["Monday", "Tuesday"]
    }

    # Constraint problem
    problem = Problem()
    days = ["Monday", "Tuesday"]
    all_starts = sorted(set(allowed_starts["Monday"] + allowed_starts["Tuesday"]))

    problem.addVariable("Day", days)
    problem.addVariable("Start", all_starts)

    # Start must be allowed for the chosen day
    def allowed_for_day(day, start):
        return start in allowed_starts[day]

    problem.addConstraint(allowed_for_day, ("Day", "Start"))

    solutions = problem.getSolutions()

    # Preferences:
    # - Avoid Monday
    # - Avoid Tuesday before 14:30 (i.e., prefer Tuesday at or after 14:30)
    def preference_key(sol):
        day = sol["Day"]
        start = sol["Start"]
        # Highest priority: Tuesday at or after 14:30
        if day == "Tuesday" and start >= time_to_minutes("14:30"):
            return (0, start)  # earliest after 14:30 preferred
        # Next: any Tuesday
        if day == "Tuesday":
            return (1, start)
        # Last: Monday
        return (2, start)

    best = min(solutions, key=preference_key)

    day = best["Day"]
    start = best["Start"]
    end = start + MEETING_DURATION_MIN

    time_range_plain = f"{minutes_to_time(start)}:{minutes_to_time(end)}"
    time_range_braced = f"{{{minutes_to_time(start)}:{minutes_to_time(end)}}}"

    # Output must include both the time range and the day of the week
    print(time_range_plain)
    print(day)
    print(f"{day} {time_range_braced}")

if __name__ == "__main__":
    main()