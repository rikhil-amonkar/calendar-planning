# Requires: python-constraint
from constraint import Problem

def to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def from_min(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def build_minutes(busy_dict):
    out = {}
    for day, intervals in busy_dict.items():
        out[day] = [(to_min(s), to_min(e)) for s, e in intervals]
    return out

def overlaps(a_start, a_end, b_start, b_end):
    return a_start < b_end and a_end > b_start

def main():
    days = ["Monday", "Tuesday", "Wednesday"]
    meeting_duration = 30  # minutes
    work_start = to_min("09:00")
    work_end = to_min("17:00")

    # Participants' busy schedules
    joshua_busy = {
        "Monday":   [("15:00", "15:30")],
        "Tuesday":  [("11:30", "12:00"), ("13:00", "13:30"), ("14:30", "15:00")],
        "Wednesday": []
    }
    joyce_busy = {
        "Monday":   [("09:00", "09:30"), ("10:00", "11:00"), ("11:30", "12:30"),
                     ("13:00", "15:00"), ("15:30", "17:00")],
        "Tuesday":  [("09:00", "17:00")],
        "Wednesday":[("09:00", "09:30"), ("10:00", "11:00"),
                     ("12:30", "15:30"), ("16:00", "16:30")]
    }

    joshua_busy_min = build_minutes(joshua_busy)
    joyce_busy_min = build_minutes(joyce_busy)

    # Domain for start times in 30-minute increments within work hours
    start_times = []
    t = work_start
    while t + meeting_duration <= work_end:
        start_times.append(t)
        t += 30

    problem = Problem()
    problem.addVariable("day", days)
    problem.addVariable("start", start_times)

    # Constraint: no overlap with existing meetings for both participants
    def no_conflicts(day, start):
        end = start + meeting_duration
        for s, e in joshua_busy_min[day]:
            if overlaps(start, end, s, e):
                return False
        for s, e in joyce_busy_min[day]:
            if overlaps(start, end, s, e):
                return False
        return True

    # Constraint: Joyce would rather not meet on Monday before 12:00 (treat as hard)
    def monday_after_noon_for_joyce(day, start):
        if day == "Monday" and start < to_min("12:00"):
            return False
        return True

    problem.addConstraint(no_conflicts, ("day", "start"))
    problem.addConstraint(monday_after_noon_for_joyce, ("day", "start"))

    solutions = problem.getSolutions()
    if not solutions:
        raise SystemExit("No feasible meeting time found.")

    # Prefer Wednesday if available, then Monday, then Tuesday; earliest time within the chosen day
    day_priority = {"Wednesday": 0, "Monday": 1, "Tuesday": 2}
    solutions.sort(key=lambda sol: (day_priority[sol["day"]], sol["start"]))

    best = solutions[0]
    day = best["day"]
    start = best["start"]
    end = start + meeting_duration

    # Output: day and time range in {HH:MM:HH:MM}
    print(day)
    print(f"{{{from_min(start)}:{from_min(end)}}}")

if __name__ == "__main__":
    main()