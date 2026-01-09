# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

def minutes(hh_mm):
    hh, mm = map(int, hh_mm.split(":"))
    return hh * 60 + mm

def fmt(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def no_overlap_constraint(busy_map, duration):
    def _constraint(day, start):
        end = start + duration
        for bs, be in busy_map.get(day, []):
            # overlap if intervals intersect
            if start < be and end > bs:
                return False
        return True
    return _constraint

def main():
    problem = Problem()

    # Meeting parameters
    duration = 30  # minutes
    work_start = minutes("09:00")
    work_end = minutes("17:00")

    # Days under consideration
    days = ["Monday", "Tuesday", "Wednesday"]

    # Busy schedules (minutes from midnight)
    cheryl_busy = {
        "Monday": [
            (minutes("09:00"), minutes("09:30")),
            (minutes("11:30"), minutes("13:00")),
            (minutes("15:30"), minutes("16:00")),
        ],
        "Tuesday": [
            (minutes("15:00"), minutes("15:30")),
        ],
        # Cheryl cannot meet on Wednesday (handled via constraint)
    }

    kyle_busy = {
        "Monday": [
            (minutes("09:00"), minutes("17:00")),
        ],
        "Tuesday": [
            (minutes("09:30"), minutes("17:00")),
        ],
        "Wednesday": [
            (minutes("09:00"), minutes("09:30")),
            (minutes("10:00"), minutes("13:00")),
            (minutes("13:30"), minutes("14:00")),
            (minutes("14:30"), minutes("17:00")),
        ],
    }

    # Variables
    problem.addVariable("day", days)
    # Start times in 30-minute increments within work hours ensuring end <= 17:00
    starts = list(range(work_start, work_end - duration + 1, 30))
    problem.addVariable("start", starts)

    # Constraints:
    # 1) Cheryl cannot meet on Wednesday
    problem.addConstraint(lambda d: d != "Wednesday", ["day"])

    # 2) Respect each participant's busy schedule
    problem.addConstraint(no_overlap_constraint(cheryl_busy, duration), ["day", "start"])
    problem.addConstraint(no_overlap_constraint(kyle_busy, duration), ["day", "start"])

    # Solve and pick the earliest valid slot (by day order then time)
    solutions = problem.getSolutions()

    if not solutions:
        print("No feasible meeting time found.")
        return

    day_order = {"Monday": 0, "Tuesday": 1, "Wednesday": 2}
    solutions.sort(key=lambda s: (day_order[s["day"]], s["start"]))

    chosen = solutions[0]
    start = chosen["start"]
    end = start + duration
    day = chosen["day"]

    # Output: include both time range and day of the week
    # Time range format: {HH:MM:HH:MM}
    print(day)
    print(f"{{{fmt(start)}:{fmt(end)}}}")

if __name__ == "__main__":
    main()