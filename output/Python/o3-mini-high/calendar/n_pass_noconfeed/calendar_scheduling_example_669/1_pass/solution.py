def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Meeting parameters
meeting_duration = 30  # in minutes
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
preferred_end_monday = time_to_minutes("14:00")  # Doris prefers meetings to finish by 14:00 on Monday

# Busy schedules represented as (start, end) in minutes
busy_schedules = {
    "Monday": {
        "Jean": [],  # Jean is free on Monday
        "Doris": [
            (time_to_minutes("09:00"), time_to_minutes("11:30")),
            (time_to_minutes("12:00"), time_to_minutes("12:30")),
            (time_to_minutes("13:30"), time_to_minutes("16:00")),
            (time_to_minutes("16:30"), time_to_minutes("17:00")),
        ],
    },
    "Tuesday": {
        "Jean": [
            (time_to_minutes("11:30"), time_to_minutes("12:00")),
            (time_to_minutes("16:00"), time_to_minutes("16:30")),
        ],
        "Doris": [
            (time_to_minutes("09:00"), time_to_minutes("17:00"))
        ],
    },
}

def get_free_intervals(busy, start=work_start, end=work_end):
    free_intervals = []
    current = start
    for interval in sorted(busy, key=lambda x: x[0]):
        busy_start, busy_end = interval
        if current < busy_start:
            free_intervals.append((current, busy_start))
        current = max(current, busy_end)
    if current < end:
        free_intervals.append((current, end))
    return free_intervals

def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if end - start >= meeting_duration:
            intersections.append((start, end))
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return intersections

meeting_day = None
meeting_start = None
meeting_end = None

# Try scheduling on Monday first, then Tuesday.
for day in ["Monday", "Tuesday"]:
    free_jean = get_free_intervals(busy_schedules[day]["Jean"])
    free_doris = get_free_intervals(busy_schedules[day]["Doris"])
    
    common_free = intersect_intervals(free_jean, free_doris)
    
    for interval in common_free:
        start_int, end_int = interval
        # Check if this interval can host the meeting
        if start_int + meeting_duration <= end_int:
            # On Monday, respect Doris's preference to avoid meetings after 14:00.
            if day == "Monday":
                if start_int + meeting_duration <= preferred_end_monday:
                    meeting_start = start_int
                    meeting_end = start_int + meeting_duration
                    meeting_day = day
                    break
                else:
                    # Try to adjust start time within the interval so it ends by 14:00.
                    adjusted_start = preferred_end_monday - meeting_duration
                    if adjusted_start >= start_int and adjusted_start + meeting_duration <= end_int:
                        meeting_start = adjusted_start
                        meeting_end = adjusted_start + meeting_duration
                        meeting_day = day
                        break
            else:
                meeting_start = start_int
                meeting_end = start_int + meeting_duration
                meeting_day = day
                break
    if meeting_day is not None:
        break

if meeting_day:
    # Format the result as HH:MM:HH:MM with the day of the week.
    output = f"{meeting_day} {minutes_to_time_str(meeting_start)}:{minutes_to_time_str(meeting_end)}"
    print(output)
else:
    print("No available meeting time found.")