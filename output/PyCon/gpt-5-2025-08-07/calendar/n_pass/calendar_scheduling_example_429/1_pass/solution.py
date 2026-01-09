# Requires: python-constraint
from constraint import Problem

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def overlaps(a_start, a_end, b_start, b_end):
    return max(a_start, b_start) < min(a_end, b_end)

def main():
    day = "Monday"
    meeting_duration = 30  # minutes
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")

    busy = {
        "Judy":       [("13:00", "13:30"), ("16:00", "16:30")],
        "Olivia":     [("10:00", "10:30"), ("12:00", "13:00"), ("14:00", "14:30")],
        "Eric":       [],
        "Jacqueline": [("10:00", "10:30"), ("15:00", "15:30")],
        "Laura":      [("09:00", "10:00"), ("10:30", "12:00"), ("13:00", "13:30"),
                       ("14:30", "15:00"), ("15:30", "17:00")],
        "Tyler":      [("09:00", "10:00"), ("11:00", "11:30"), ("12:30", "13:00"),
                       ("14:00", "14:30"), ("15:30", "17:00")],
        "Lisa":       [("09:30", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"),
                       ("13:00", "13:30"), ("14:00", "14:30"), ("16:00", "17:00")],
    }

    # Convert busy intervals to minutes
    busy_minutes = {
        person: [(time_to_minutes(s), time_to_minutes(e)) for s, e in intervals]
        for person, intervals in busy.items()
    }

    # Domain: starts at 30-min increments within working hours, ensuring meeting fits fully
    domain_starts = list(range(work_start, work_end - meeting_duration + 1, 30))

    problem = Problem()
    problem.addVariable("start", domain_starts)

    def all_available(start):
        end = start + meeting_duration
        if end > work_end or start < work_start:
            return False
        for intervals in busy_minutes.values():
            for b_start, b_end in intervals:
                if overlaps(start, end, b_start, b_end):
                    return False
        return True

    problem.addConstraint(all_available, ["start"])

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No feasible meeting time found.")

    # Choose the earliest feasible time
    best_start = min(sol["start"] for sol in solutions)
    best_end = best_start + meeting_duration

    start_str = minutes_to_time(best_start)
    end_str = minutes_to_time(best_end)
    time_range = f"{start_str}:{end_str}"

    # Output both the day and the time range in braces, as required
    print(day)
    print(f"{{{time_range}}}")

if __name__ == "__main__":
    main()