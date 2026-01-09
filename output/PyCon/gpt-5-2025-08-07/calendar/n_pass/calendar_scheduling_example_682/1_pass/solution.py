# Requires: python-constraint
# pip install python-constraint

from constraint import Problem
from datetime import datetime, timedelta

def to_minutes(tstr):
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

def to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def add_minutes(tstr, mins):
    return to_time_str(to_minutes(tstr) + mins)

def overlaps(a_start, a_end, b_start, b_end):
    return a_start < b_end and a_end > b_start

# Busy schedules
busy = {
    "Amanda": {
        "Monday": [
            ("09:00", "10:30"),
            ("11:00", "11:30"),
            ("12:30", "13:00"),
            ("13:30", "14:00"),
            ("14:30", "15:00"),
        ],
        "Tuesday": [
            ("09:00", "09:30"),
            ("10:00", "10:30"),
            ("11:30", "12:00"),
            ("13:30", "14:30"),
            ("15:30", "16:00"),
            ("16:30", "17:00"),
        ],
    },
    "Nathan": {
        "Monday": [
            ("10:00", "10:30"),
            ("11:00", "11:30"),
            ("13:30", "14:30"),
            ("16:00", "16:30"),
        ],
        "Tuesday": [
            ("09:00", "10:30"),
            ("11:00", "13:00"),
            ("13:30", "14:00"),
            ("14:30", "15:30"),
            ("16:00", "16:30"),
        ],
    },
}

meeting_duration = 30  # minutes
work_start = "09:00"
work_end = "17:00"
days = ["Monday", "Tuesday"]

# Domain of candidate start times in 30-minute increments within work hours
domain_times = []
start_min = to_minutes(work_start)
end_min = to_minutes(work_end) - meeting_duration  # last start so meeting ends by 17:00
t = start_min
while t <= end_min:
    domain_times.append(to_time_str(t))
    t += 30

problem = Problem()
problem.addVariable("Day", days)
problem.addVariable("Start", domain_times)

def availability_constraint(day, start):
    # Nathan cannot meet on Monday
    if day == "Monday":
        return False

    start_m = to_minutes(start)
    end_m = start_m + meeting_duration

    # Amanda does not want to meet on Tuesday after 11:00
    if day == "Tuesday":
        eleven = to_minutes("11:00")
        if end_m > eleven:
            return False

    # Check busy overlaps for both participants on the chosen day
    for person in ["Amanda", "Nathan"]:
        for b_start, b_end in busy[person][day]:
            b_s = to_minutes(b_start)
            b_e = to_minutes(b_end)
            if overlaps(start_m, end_m, b_s, b_e):
                return False

    return True

problem.addConstraint(availability_constraint, ["Day", "Start"])

solutions = problem.getSolutions()

if not solutions:
    print("No feasible meeting time found.")
else:
    # Choose the earliest valid time (sort by day order then start time)
    day_order = {d: i for i, d in enumerate(days)}
    solutions.sort(key=lambda s: (day_order[s["Day"]], to_minutes(s["Start"])))
    sol = solutions[0]
    start = sol["Start"]
    end = add_minutes(start, meeting_duration)
    day = sol["Day"]
    # Output day and time range in required format
    print(day)
    print(f"{{{start}:{end}}}")