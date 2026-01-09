from constraint import Problem

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def no_overlap(start, busy_intervals, duration=60):
    end = start + duration
    for bs, be in busy_intervals:
        if max(start, bs) < min(end, be):
            return False
    return True

def main():
    day = "Monday"
    meeting_duration = 60  # minutes
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")

    # Busy schedules (converted to minutes)
    Anthony_busy = [(to_minutes("09:30"), to_minutes("10:00")),
                    (to_minutes("12:00"), to_minutes("13:00")),
                    (to_minutes("16:00"), to_minutes("16:30"))]

    Pamela_busy = [(to_minutes("09:30"), to_minutes("10:00")),
                   (to_minutes("16:30"), to_minutes("17:00"))]

    Zachary_busy = [(to_minutes("09:00"), to_minutes("11:30")),
                    (to_minutes("12:00"), to_minutes("12:30")),
                    (to_minutes("13:00"), to_minutes("13:30")),
                    (to_minutes("14:30"), to_minutes("15:00")),
                    (to_minutes("16:00"), to_minutes("17:00"))]

    # Pamela preference: do not meet after 14:30 → meeting must end by 14:30
    pamela_latest_end = to_minutes("14:30")

    # Build domain of possible start times in 30-minute increments
    starts = list(range(work_start, work_end - meeting_duration + 1, 30))

    problem = Problem()
    problem.addVariable("start", starts)

    # Working hours constraint implicitly handled by domain, but ensure end within work hours
    problem.addConstraint(lambda s: s + meeting_duration <= work_end, ["start"])

    # Individual availability constraints
    problem.addConstraint(lambda s, b=Anthony_busy: no_overlap(s, b, meeting_duration), ["start"])
    problem.addConstraint(lambda s, b=Pamela_busy: no_overlap(s, b, meeting_duration), ["start"])
    problem.addConstraint(lambda s, b=Zachary_busy: no_overlap(s, b, meeting_duration), ["start"])

    # Pamela's preference constraint (end by 14:30)
    problem.addConstraint(lambda s: s + meeting_duration <= pamela_latest_end, ["start"])

    solutions = problem.getSolutions()
    if not solutions:
        print("No solution found")
        return

    # Choose the earliest valid start time
    start_time = min(sol["start"] for sol in solutions)
    end_time = start_time + meeting_duration

    print(f"{day} {{{to_hhmm(start_time)}:{to_hhmm(end_time)}}}")

if __name__ == "__main__":
    main()