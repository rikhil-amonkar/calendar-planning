def time_to_minutes(t):
    """Convert HH:MM string to minutes from midnight."""
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes from midnight to HH:MM string."""
    return f"{m // 60:02d}:{m % 60:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    """Given busy intervals (list of (start, end) in minutes, assumed unsorted) return free intervals within work hours."""
    # Sort busy intervals by start time
    busy_sorted = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current = work_start
    for b_start, b_end in busy_sorted:
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """Return the intersection intervals between two lists of intervals."""
    intersections = []
    for start1, end1 in intervals1:
        for start2, end2 in intervals2:
            start = max(start1, start2)
            end = min(end1, end2)
            if start < end:
                intersections.append((start, end))
    return intersections

# Define the busy schedules for each participant in HH:MM strings.
schedules = {
    "Laura": {
        "Monday": [("10:30", "11:00"), ("12:30", "13:00"), ("14:30", "15:30"), ("16:00", "17:00")],
        "Tuesday": [("9:30", "10:00"), ("11:00", "11:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("16:00", "17:00")],
        "Wednesday": [("11:30", "12:00"), ("12:30", "13:00"), ("15:30", "16:30")],
        "Thursday": [("10:30", "11:00"), ("12:00", "13:30"), ("15:00", "15:30"), ("16:00", "16:30")]
    },
    "Philip": {
        "Monday": [("9:00", "17:00")],
        "Tuesday": [("9:00", "11:00"), ("11:30", "12:00"), ("13:00", "13:30"), ("14:00", "14:30"), ("15:00", "16:30")],
        "Wednesday": [("9:00", "10:00"), ("11:00", "12:00"), ("12:30", "16:00"), ("16:30", "17:00")],
        "Thursday": [("9:00", "10:30"), ("11:00", "12:30"), ("13:00", "17:00")]
    }
}

# Meeting constraints
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 60  # minutes

# The days to consider: Monday, Tuesday, Wednesday, Thursday
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Philip cannot meet on Wednesday -> skip Wednesday
meeting_found = False
for day in days:
    if day == "Wednesday":
        continue

    # Get busy intervals for each participant for this day and convert to minutes.
    laura_busy = [(time_to_minutes(start), time_to_minutes(end)) for start, end in schedules["Laura"].get(day, [])]
    philip_busy = [(time_to_minutes(start), time_to_minutes(end)) for start, end in schedules["Philip"].get(day, [])]

    # Compute free intervals for each participant
    laura_free = get_free_intervals(laura_busy, work_start, work_end)
    philip_free = get_free_intervals(philip_busy, work_start, work_end)

    # Find intersecting free intervals
    common_free = intersect_intervals(laura_free, philip_free)

    # Check if any common interval has enough time for the meeting.
    for start, end in sorted(common_free, key=lambda x: x[0]):
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = meeting_start + meeting_duration
            print(f"{day} {minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
            meeting_found = True
            break
    if meeting_found:
        break

if not meeting_found:
    print("No available meeting time found.")