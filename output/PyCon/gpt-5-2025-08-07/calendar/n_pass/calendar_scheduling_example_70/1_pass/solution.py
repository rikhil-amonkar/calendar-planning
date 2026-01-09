from constraint import Problem

def to_minutes(hh_mm):
    h, m = map(int, hh_mm.split(":"))
    return h * 60 + m

def to_hhmm(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def no_overlap(start, duration, busy_intervals):
    end = start + duration
    for b_start, b_end in busy_intervals:
        if start < b_end and end > b_start:
            return False
    return True

if __name__ == "__main__":
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    meeting_duration = 30  # minutes

    # Busy schedules (start, end) in minutes
    denise_busy = [
        (to_minutes("12:00"), to_minutes("12:30")),
        (to_minutes("15:30"), to_minutes("16:00")),
    ]
    angela_busy = []  # No meetings
    natalie_busy = [
        (to_minutes("09:00"), to_minutes("11:30")),
        (to_minutes("12:00"), to_minutes("13:00")),
        (to_minutes("14:00"), to_minutes("14:30")),
        (to_minutes("15:00"), to_minutes("17:00")),
    ]

    # Domain: possible start times at 30-minute granularity
    domain = list(range(work_start, work_end - meeting_duration + 1, 30))

    problem = Problem()
    problem.addVariable("start", domain)

    def all_available(start):
        return (
            no_overlap(start, meeting_duration, denise_busy) and
            no_overlap(start, meeting_duration, angela_busy) and
            no_overlap(start, meeting_duration, natalie_busy)
        )

    problem.addConstraint(all_available, ["start"])

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No feasible meeting time found.")

    earliest_start = min(sol["start"] for sol in solutions)
    start_str = to_hhmm(earliest_start)
    end_str = to_hhmm(earliest_start + meeting_duration)

    # Outputs
    # 1) HH:MM:HH:MM
    print(f"{start_str}:{end_str}")
    # 2) Day of the week
    print(day)
    # 3) Curly-brace time range as requested example format
    print(f"{{{start_str}:{end_str}}}")