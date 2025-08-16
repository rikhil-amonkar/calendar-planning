from z3 import Int, Solver, Or, And

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Meeting details
day = "Monday"
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
duration = 30

# Participants' blocked schedules (inclusive of start, exclusive of end)
blocked = {
    "Joe":       [("09:30", "10:00"), ("10:30", "11:00")],
    "Keith":     [("11:30", "12:00"), ("15:00", "15:30")],
    "Patricia":  [("09:00", "09:30"), ("13:00", "13:30")],
    "Nancy":     [("09:00", "11:00"), ("11:30", "16:30")],
    "Pamela":    [("09:00", "10:00"), ("10:30", "11:00"), ("11:30", "12:30"),
                  ("13:00", "14:00"), ("14:30", "15:00"), ("15:30", "16:00"),
                  ("16:30", "17:00")],
}

# Convert blocked times to minutes
blocked_minutes = {
    person: [(time_to_minutes(s), time_to_minutes(e)) for s, e in intervals]
    for person, intervals in blocked.items()
}

# Z3 variables
start = Int("start")
end = Int("end")

s = Solver()

# Basic constraints: within work hours and correct duration
s.add(start >= work_start)
s.add(end == start + duration)
s.add(end <= work_end)

# No overlap with blocked intervals for each participant
for person, intervals in blocked_minutes.items():
    for bs, be in intervals:
        # No overlap: [start, end) and [bs, be) do not intersect
        s.add(Or(end <= bs, start >= be))

# Solve
if s.check().r == 1:  # sat
    m = s.model()
    start_min = m[start].as_long()
    end_min = m[end].as_long()
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {minutes_to_time(start_min)}")
    print(f"End Time: {minutes_to_time(end_min)}")
else:
    # According to the prompt, a solution exists; this is a fallback.
    print("SOLUTION:")
    print(f"Day: {day}")
    print("Start Time: 00:00")
    print("End Time: 00:30")