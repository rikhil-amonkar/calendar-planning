from datetime import datetime, timedelta

def time_to_minutes(t_str):
    # t_str format "HH:MM"
    h, m = map(int, t_str.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def get_free_slots(busy_slots, work_start, work_end):
    """Return free time intervals (in minutes) given busy slots (list of (start, end) in minutes)."""
    free = []
    current = work_start
    # Sort busy slots by their starting times
    busy_slots.sort()
    for start, end in busy_slots:
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_slots(slots1, slots2):
    """Return list of intersections between two lists of intervals (in minutes)."""
    intersections = []
    i, j = 0, 0
    while i < len(slots1) and j < len(slots2):
        a_start, a_end = slots1[i]
        b_start, b_end = slots2[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            intersections.append((start, end))
        # move pointer with the earlier ending slot
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return intersections

# Define work hours in minutes (9:00 to 17:00)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 60  # in minutes

# Define busy schedules as dictionaries by day for Betty and Megan.
# Times are in HH:MM format and will be converted to minutes.
busy_betty = {
    "Monday": [("10:00", "10:30"), ("11:30", "12:30"), ("16:00", "16:30")],
    "Tuesday": [("9:30", "10:00"), ("10:30", "11:00"), ("12:00", "12:30"), ("13:30", "15:00"), ("16:30", "17:00")],
    # Betty cannot meet on Wednesday, so we omit it.
    # Skip Thursday as Betty cannot meet.
    "Friday": [("9:00", "10:00"), ("11:30", "12:00"), ("12:30", "13:00"), ("14:30", "15:00")]
}

busy_megan = {
    "Monday": [("09:00", "17:00")],
    "Tuesday": [("09:00", "9:30"), ("10:00", "10:30"), ("12:00", "14:00"), ("15:00", "15:30"), ("16:00", "16:30")],
    # Wednesday is not an option because Betty is unavailable.
    "Thursday": [("09:00", "10:30"), ("11:30", "14:00"), ("14:30", "15:00"), ("15:30", "16:30")],
    "Friday": [("09:00", "17:00")]
}

# We consider possible days: Monday, Tuesday, Friday.
# (Monday and Friday are ruled out for Megan, Monday and Friday Megan is busy all day.)
# Only Tuesday remains a candidate where both can meet.
candidate_days = ["Monday", "Tuesday", "Friday"]

meeting_day = None
meeting_start_min = None
meeting_end_min = None

for day in candidate_days:
    # Skip days that are not allowed for Betty
    if day in ["Wednesday", "Thursday"]:
        continue
        
    # Get free slots for Betty
    betty_busy = busy_betty.get(day, [])
    betty_busy_minutes = [(time_to_minutes(s), time_to_minutes(e)) for s, e in betty_busy]
    betty_free = get_free_slots(betty_busy_minutes, work_start, work_end)
    
    # Get free slots for Megan
    megan_busy = busy_megan.get(day, [])
    megan_busy_minutes = [(time_to_minutes(s), time_to_minutes(e)) for s, e in megan_busy]
    megan_free = get_free_slots(megan_busy_minutes, work_start, work_end)
    
    # Find intersections between Betty's free slots and Megan's free slots
    common_free = intersect_slots(betty_free, megan_free)
    
    # Check if any intersection can accommodate meeting duration
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_day = day
            meeting_start_min = start
            meeting_end_min = start + meeting_duration
            break
    if meeting_day:
        break

if meeting_day:
    meeting_start_str = minutes_to_time(meeting_start_min)
    meeting_end_str = minutes_to_time(meeting_end_min)
    # Output format: HH:MM:HH:MM and day of week
    print(f"{meeting_day} {meeting_start_str}:{meeting_end_str}")
else:
    print("No available meeting slot found.")