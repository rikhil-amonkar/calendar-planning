from constraint import Problem

def minutes(h, m):
    return h * 60 + m

def overlaps(a_start, a_end, b_start, b_end):
    return not (a_end <= b_start or b_end <= a_start)

def format_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Meeting parameters
    duration = 60  # minutes
    work_start = minutes(9, 0)
    work_end = minutes(17, 0)
    allowed_starts = list(range(work_start, work_end - duration + 1, 30))  # 30-min increments

    days = ["Monday", "Tuesday"]

    # Busy schedules (start, end) in minutes from 00:00
    gary_busy = {
        "Monday": [
            (minutes(9, 30), minutes(10, 0)),
            (minutes(11, 0), minutes(13, 0)),
            (minutes(14, 0), minutes(14, 30)),
            (minutes(16, 30), minutes(17, 0)),
        ],
        "Tuesday": [
            (minutes(9, 0), minutes(9, 30)),
            (minutes(10, 30), minutes(11, 0)),
            (minutes(14, 30), minutes(16, 0)),
        ],
    }

    david_busy = {
        "Monday": [
            (minutes(9, 0), minutes(9, 30)),
            (minutes(10, 0), minutes(13, 0)),
            (minutes(14, 30), minutes(16, 30)),
        ],
        "Tuesday": [
            (minutes(9, 0), minutes(9, 30)),
            (minutes(10, 0), minutes(10, 30)),
            (minutes(11, 0), minutes(12, 30)),
            (minutes(13, 0), minutes(14, 30)),
            (minutes(15, 0), minutes(16, 0)),
            (minutes(16, 30), minutes(17, 0)),
        ],
    }

    problem = Problem()
    problem.addVariable("day", days)
    problem.addVariable("start", allowed_starts)

    def availability(day, start):
        end = start + duration
        # within work hours
        if not (work_start <= start and end <= work_end):
            return False
        # check Gary
        for bs, be in gary_busy[day]:
            if overlaps(start, end, bs, be):
                return False
        # check David
        for bs, be in david_busy[day]:
            if overlaps(start, end, bs, be):
                return False
        return True

    problem.addConstraint(availability, ("day", "start"))

    solutions = problem.getSolutions()

    if not solutions:
        # As per prompt, a solution exists, but handle just in case
        print("No solution found")
        return

    day_order = {d: i for i, d in enumerate(days)}
    solutions.sort(key=lambda s: (day_order[s["day"]], s["start"]))

    chosen = solutions[0]
    day = chosen["day"]
    start = chosen["start"]
    end = start + duration

    start_str = format_time(start)
    end_str = format_time(end)

    print(day)
    print(f"{{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()