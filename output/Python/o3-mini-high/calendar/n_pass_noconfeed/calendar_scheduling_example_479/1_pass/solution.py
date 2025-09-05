def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hrs = minutes // 60
    mins = minutes % 60
    return f"{hrs:02d}:{mins:02d}"

def compute_free_intervals(busy, start, end):
    free = []
    current = start
    for bstart, bend in sorted(busy, key=lambda x: x[0]):
        if bstart > current:
            free.append((current, bstart))
        current = max(current, bend)
    if current < end:
        free.append((current, end))
    return free

def intersect_intervals(intervals1, intervals2):
    result = []
    for s1, e1 in intervals1:
        for s2, e2 in intervals2:
            s = max(s1, s2)
            e = min(e1, e2)
            if s < e:
                result.append((s, e))
    return result

# Define work day and meeting duration
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 60  # in minutes

# Define each participant's busy times (times in HH:MM format)
participants_busy = {
    "Evelyn": [],
    "Joshua": [
        (time_to_minutes("11:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:30"), time_to_minutes("14:30")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    "Kevin": [],
    "Gerald": [],
    "Jerry": [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("10:30"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00"))
    ],
    "Jesse": [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("10:30"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:30"))
    ],
    "Kenneth": [
        (time_to_minutes("10:30"), time_to_minutes("12:30")),
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

# Calculate free intervals for each participant within work hours.
participants_free = {}
for person, busy in participants_busy.items():
    participants_free[person] = compute_free_intervals(busy, work_start, work_end)

# Start with full workday as the initial common free time.
common_free = [(work_start, work_end)]
# Intersect all participant free intervals to get common availability.
for free in participants_free.values():
    common_free = intersect_intervals(common_free, free)
    common_free.sort(key=lambda x: x[0])

# Find the earliest common free slot that can accommodate the meeting duration.
meeting_slot = None
for start, end in common_free:
    if end - start >= meeting_duration:
        meeting_slot = (start, start + meeting_duration)
        break

if meeting_slot:
    meeting_start, meeting_end = meeting_slot
    meeting_range = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    day = "Monday"
    print(f"{day} {meeting_range}")
else:
    print("No available time found.")