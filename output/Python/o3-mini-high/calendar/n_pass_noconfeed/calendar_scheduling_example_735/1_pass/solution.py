def time_str_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time_str(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def get_free_intervals(busy, work_start, work_end):
    free = []
    current = work_start
    for start, end in busy:
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        a_start, a_end = intervals1[i]
        b_start, b_end = intervals2[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            intersections.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return intersections

def find_meeting_slot(free_intervals, duration):
    for start, end in free_intervals:
        if end - start >= duration:
            return start, start + duration
    return None

# Define work hours and meeting duration (in minutes)
work_start = time_str_to_minutes("09:00")
work_end = time_str_to_minutes("17:00")
meeting_duration = 30

# Define the blocked schedules for each participant on each day
schedules = {
    "Monday": {
        "Ronald": [("10:30", "11:00"), ("12:00", "12:30"), ("15:30", "16:00")],
        "Amber":  [("09:00", "09:30"), ("10:00", "10:30"), ("11:30", "12:00"),
                   ("12:30", "14:00"), ("14:30", "15:00"), ("15:30", "17:00")]
    },
    "Tuesday": {
        "Ronald": [("09:00", "09:30"), ("12:00", "12:30"), ("15:30", "16:30")],
        "Amber":  [("09:00", "09:30"), ("10:00", "11:30"), ("12:00", "12:30"),
                   ("13:30", "15:30"), ("16:30", "17:00")]
    },
    "Wednesday": {
        "Ronald": [("09:30", "10:30"), ("11:00", "12:00"), ("12:30", "13:00"),
                   ("13:30", "14:00"), ("16:30", "17:00")],
        "Amber":  [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "13:30"),
                   ("15:00", "15:30")]
    }
}

# We want the earliest possible slot among Monday, Tuesday, Wednesday.
for day in ["Monday", "Tuesday", "Wednesday"]:
    # Convert busy times to minutes and sort them
    busy_ronald = sorted((time_str_to_minutes(start), time_str_to_minutes(end)) for start, end in schedules[day]["Ronald"])
    busy_amber = sorted((time_str_to_minutes(start), time_str_to_minutes(end)) for start, end in schedules[day]["Amber"])
    
    free_ronald = get_free_intervals(busy_ronald, work_start, work_end)
    free_amber = get_free_intervals(busy_amber, work_start, work_end)
    
    # Find common free intervals by intersecting individual free slots.
    common_free = intersect_intervals(free_ronald, free_amber)
    
    slot = find_meeting_slot(common_free, meeting_duration)
    if slot:
        meeting_start, meeting_end = slot
        # Output in the format "HH:MM:HH:MM Day"
        print(f"{minutes_to_time_str(meeting_start)}:{minutes_to_time_str(meeting_end)} {day}")
        break