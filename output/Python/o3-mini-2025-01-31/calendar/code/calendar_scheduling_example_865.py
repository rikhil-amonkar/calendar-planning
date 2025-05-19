from datetime import timedelta, datetime

# Convert a time string "HH:MM" to minutes since midnight.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

# Convert minutes to a time string "HH:MM"
def minutes_to_time(m):
    return f"{m//60:02d}:{m%60:02d}"

# Merge overlapping intervals.
def merge_intervals(intervals):
    if not intervals:
        return []
    # sort intervals by start time
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for current in intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

# Find free time intervals within the given working hours based on busy intervals.
def find_free_intervals(busy_intervals, work_start, work_end):
    free = []
    current = work_start
    for start, end in busy_intervals:
        if current < start:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

# Define working hours (minutes) and meeting duration
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 60  # in minutes

# Define the schedules for each participant (times in HH:MM format)
schedules = {
    "Megan": {
        "Monday": [("13:00", "13:30"), ("14:00", "15:30")],
        "Tuesday": [("09:00", "09:30"), ("12:00", "12:30"), ("16:00", "17:00")],
        "Wednesday": [("09:30", "10:00"), ("10:30", "11:30"), ("12:30", "14:00"), ("16:00", "16:30")],
        "Thursday": [("13:30", "14:30"), ("15:00", "15:30")]
    },
    "Daniel": {
        "Monday": [("10:00", "11:30"), ("12:30", "15:00")],
        "Tuesday": [("09:00", "10:00"), ("10:30", "17:00")],
        "Wednesday": [("09:00", "10:00"), ("10:30", "11:30"), ("12:00", "17:00")],
        "Thursday": [("09:00", "12:00"), ("12:30", "14:30"), ("15:00", "15:30"), ("16:00", "17:00")]
    }
}

# Order of days to consider.
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

found = False

for day in days:
    # Collect busy intervals for all participants for a given day.
    busy_intervals = []
    for person in schedules:
        if day in schedules[person]:
            for interval in schedules[person][day]:
                start, end = interval
                busy_intervals.append((time_to_minutes(start), time_to_minutes(end)))
    # Merge the busy intervals.
    merged_busy = merge_intervals(busy_intervals)
    # Find free intervals within working hours.
    free_intervals = find_free_intervals(merged_busy, work_start, work_end)
    # Check if any free interval can accommodate the meeting.
    for free_start, free_end in free_intervals:
        if free_end - free_start >= meeting_duration:
            meeting_start = free_start
            meeting_end = meeting_start + meeting_duration
            print(f"{day} {minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
            found = True
            break
    if found:
        break

if not found:
    print("No available meeting slot found.")