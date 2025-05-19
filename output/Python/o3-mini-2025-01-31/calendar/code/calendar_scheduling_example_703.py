from datetime import time, timedelta, datetime

# Helper function to convert HH:MM string to minutes since midnight
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

# Helper function to convert minutes since midnight to HH:MM string
def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Define work hours in minutes
work_start = time_to_minutes("09:00")
work_end   = time_to_minutes("17:00")

# Meeting duration in minutes (60 minutes)
meeting_duration = 60

# Define the weekly schedule for participants as a dictionary.
# Each key is a day and the value is another dict with participant names mapping to a list of (start, end) meeting intervals.
schedules = {
    "Monday": {
        "Stephanie": [("09:30", "10:00"), ("10:30", "11:00"), ("11:30", "12:00"), ("14:00", "14:30")],
        "Betty":     [("09:00", "10:00"), ("11:00", "11:30"), ("14:30", "15:00"), ("15:30", "16:00")]
    },
    "Tuesday": {
        "Stephanie": [("12:00", "13:00")],
        "Betty":     [("09:00", "09:30"), ("11:30", "12:00"), ("12:30", "14:30"), ("15:30", "16:00")]
    },
    "Wednesday": {
        "Stephanie": [("09:00", "10:00"), ("13:00", "14:00")],
        "Betty":     [("10:00", "11:30"), ("12:00", "14:00"), ("14:30", "17:00")]
    }
}

# Additional participant constraints:
# Stephanie prefers to avoid Monday meetings if possible.
# Betty cannot meet on Tuesday after 12:30.
# We will try to schedule the meeting on a day considering these preferences.

# Function to get free intervals for a participant on a given day.
def get_free_intervals(meetings):
    # Convert meeting times to minutes and sort
    busy = []
    for start, end in meetings:
        busy.append((time_to_minutes(start), time_to_minutes(end)))
    busy.sort()
    
    free_intervals = []
    # begin with the work start
    current = work_start
    for s, e in busy:
        if current < s:
            free_intervals.append((current, s))
        current = max(current, e)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

# Function to compute the intersection of two lists of intervals.
def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    intersection = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        start_int = max(start1, start2)
        end_int = min(end1, end2)
        if start_int + meeting_duration <= end_int:
            intersection.append((start_int, end_int))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersection

# Try days in order: Tuesday and Wednesday are preferred because Stephanie wants to avoid Monday if possible.
preferred_days = ["Tuesday", "Wednesday", "Monday"]

meeting_day = None
meeting_start = None
meeting_end = None

for day in preferred_days:
    # Check additional constraint specific for Tuesday: Betty cannot meet after 12:30 on Tuesday.
    # This means the meeting must finish by 12:30. We'll adjust Tuesday's work_end if needed.
    day_work_end = work_end
    if day == "Tuesday":
        day_work_end = min(day_work_end, time_to_minutes("12:30"))
    
    # For each participant, get free intervals but restricted to the day's work interval (possibly modified for Tuesday).
    meeting_possible = True
    common_free = [(work_start, day_work_end)]
    
    for participant in schedules[day]:
        free = get_free_intervals(schedules[day][participant])
        # If day is Tuesday, restrict each free interval to end at day_work_end.
        if day == "Tuesday":
            free = [(max(start, work_start), min(end, day_work_end)) for start, end in free if start < day_work_end]
        # Update common_free with the intersection
        common_free = intersect_intervals(common_free, free)
        if not common_free:
            meeting_possible = False
            break

    if meeting_possible:
        # Now, search in common_free for an interval that can fit the meeting_duration.
        for start, end in common_free:
            if start + meeting_duration <= end:
                meeting_day = day
                meeting_start = start
                meeting_end = start + meeting_duration
                break
    if meeting_day:
        break

if meeting_day and meeting_start is not None:
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    print(f"{meeting_day} {start_str}:{end_str}")
else:
    print("No available meeting time found.")