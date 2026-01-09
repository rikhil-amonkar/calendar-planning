from constraint import Problem

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def no_overlap_factory(blocks, duration):
    def no_overlap(start):
        end = start + duration
        for bstart, bend in blocks:
            # Overlap occurs if start < bend and end > bstart
            if start < bend and end > bstart:
                return False
        return True
    return no_overlap

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 30  # minutes

    # Busy schedules (inclusive of start, exclusive of end)
    schedules = {
        "Eric": [],
        "Ashley": [
            (to_minutes("10:00"), to_minutes("10:30")),
            (to_minutes("11:00"), to_minutes("12:00")),
            (to_minutes("12:30"), to_minutes("13:00")),
            (to_minutes("15:00"), to_minutes("16:00")),
        ],
        "Ronald": [
            (to_minutes("09:00"), to_minutes("09:30")),
            (to_minutes("10:00"), to_minutes("11:30")),
            (to_minutes("12:30"), to_minutes("14:00")),
            (to_minutes("14:30"), to_minutes("17:00")),
        ],
        "Larry": [
            (to_minutes("09:00"), to_minutes("12:00")),
            (to_minutes("13:00"), to_minutes("17:00")),
        ],
    }

    # Define CSP
    problem = Problem()

    # Start times at 30-minute increments within work hours
    domain = list(range(work_start, work_end - duration + 1, 30))
    problem.addVariable("start", domain)

    # Add constraints for each participant
    for blocks in schedules.values():
        problem.addConstraint(no_overlap_factory(blocks, duration), ["start"])

    # Solve and choose the earliest valid start time
    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No feasible meeting time found.")
    earliest_start = min(sol["start"] for sol in solutions)
    end_time = earliest_start + duration

    # Output format: Day {HH:MM:HH:MM}
    print(f"{day} {{{fmt(earliest_start)}:{fmt(end_time)}}}")

if __name__ == "__main__":
    main()