from constraint import Problem

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def to_hhmm(minutes):
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

def no_overlap(start_minute, busy_intervals):
    meeting_end = start_minute + 30
    for b_start, b_end in busy_intervals:
        if start_minute < b_end and meeting_end > b_start:
            return False
    return True

def main():
    # Work hours and meeting duration
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 30

    # Domain: all 30-minute start times fully within work hours
    domain = list(range(work_start, work_end - duration + 1, 30))

    # Participants' busy schedules (inclusive of start, exclusive of end)
    schedules = {
        "Wayne": [],  # Free entire day; preference handled separately
        "Melissa": [
            (to_minutes("10:00"), to_minutes("11:00")),
            (to_minutes("12:30"), to_minutes("14:00")),
            (to_minutes("15:00"), to_minutes("15:30")),
        ],
        "Catherine": [],  # Free entire day
        "Gregory": [
            (to_minutes("12:30"), to_minutes("13:00")),
            (to_minutes("15:30"), to_minutes("16:00")),
        ],
        "Victoria": [
            (to_minutes("09:00"), to_minutes("09:30")),
            (to_minutes("10:30"), to_minutes("11:30")),
            (to_minutes("13:00"), to_minutes("14:00")),
            (to_minutes("14:30"), to_minutes("15:00")),
            (to_minutes("15:30"), to_minutes("16:30")),
        ],
        "Thomas": [
            (to_minutes("10:00"), to_minutes("12:00")),
            (to_minutes("12:30"), to_minutes("13:00")),
            (to_minutes("14:30"), to_minutes("16:00")),
        ],
        "Jennifer": [
            (to_minutes("09:00"), to_minutes("09:30")),
            (to_minutes("10:00"), to_minutes("10:30")),
            (to_minutes("11:00"), to_minutes("13:00")),
            (to_minutes("13:30"), to_minutes("14:30")),
            (to_minutes("15:00"), to_minutes("15:30")),
            (to_minutes("16:00"), to_minutes("16:30")),
        ],
    }

    # Set up CSP
    problem = Problem()
    problem.addVariable("start", domain)

    # Hard constraints: no overlap with any participant's busy intervals
    for participant, busy in schedules.items():
        if busy:
            problem.addConstraint(lambda s, intervals=busy: no_overlap(s, intervals), ("start",))

    # Preference constraint: Wayne would like to avoid meetings before 14:00
    problem.addConstraint(lambda s: s >= to_minutes("14:00"), ("start",))

    # Find all feasible solutions and choose the earliest
    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No feasible meeting time found.")

    best_start = min(sol["start"] for sol in solutions)
    best_end = best_start + duration

    # Output: include day and time range in {HH:MM:HH:MM} format
    print(f"{day} {{{to_hhmm(best_start)}:{to_hhmm(best_end)}}}")

if __name__ == "__main__":
    main()