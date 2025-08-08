# Meeting scheduler for Monday between 09:00 and 17:00, duration 30 minutes.

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt(m):
    return f"{m//60:02d}:{m%60:02d}"

def overlaps(a_start, a_end, b_start, b_end):
    # Half-open intervals: [start, end)
    return max(a_start, b_start) < min(a_end, b_end)

day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30
step = 30  # check on half-hour increments

schedules = {
    "Megan":     [("09:00","09:30"), ("10:00","11:00"), ("12:00","12:30")],
    "Christine": [("09:00","09:30"), ("11:30","12:00"), ("13:00","14:00"), ("15:30","16:30")],
    "Gabriel":   [],  # free all day
    "Sara":      [("11:30","12:00"), ("14:30","15:00")],
    "Bruce":     [("09:30","10:00"), ("10:30","12:00"), ("12:30","14:00"), ("14:30","15:00"), ("15:30","16:30")],
    "Kathryn":   [("10:00","15:30"), ("16:00","16:30")],
    "Billy":     [("09:00","09:30"), ("11:00","11:30"), ("12:00","14:00"), ("14:30","15:30")],
}

# Convert busy schedules to minutes and clamp to work hours
busy_minutes = {}
for person, intervals in schedules.items():
    mins = []
    for s, e in intervals:
        start = max(work_start, to_minutes(s))
        end = min(work_end, to_minutes(e))
        if start < end:
            mins.append((start, end))
    busy_minutes[person] = mins

# Search for earliest feasible start
proposed = None
for start in range(work_start, work_end - duration + 1, step):
    end = start + duration
    feasible = True
    for person, intervals in busy_minutes.items():
        if any(overlaps(start, end, b_start, b_end) for b_start, b_end in intervals):
            feasible = False
            break
    if feasible:
        proposed = (start, end)
        break

if not proposed:
    raise SystemExit("No available time slot found.")

start_str = fmt(proposed[0])
end_str = fmt(proposed[1])

# Output in required formats:
print(f"{start_str}:{end_str}")
print(day)