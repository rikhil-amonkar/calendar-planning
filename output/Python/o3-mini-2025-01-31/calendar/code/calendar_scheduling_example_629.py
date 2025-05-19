from datetime import datetime, timedelta

# Meeting duration in minutes
meeting_duration = timedelta(minutes=30)

# Work hours for Tuesday (since Margaret does not want Monday)
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Constraint: The meeting must finish before 14:30 on Tuesday.
latest_meeting_end = datetime.strptime("14:30", "%H:%M")

# Define busy intervals for each participant on Tuesday (start, end)
# Times are given as strings in HH:MM format.
# Margaret's schedule on Tuesday
margaret_busy = [
    (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M"))
]

# Alexis's schedule on Tuesday
alexis_busy = [
    (datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
    (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
    (datetime.strptime("14:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))
]

def get_free_slots(busy_slots, start, end):
    """Return a list of free time intervals (start, end) given a sorted busy_slots."""
    free_slots = []
    current = start
    for busy in sorted(busy_slots):
        busy_start, busy_end = busy
        if busy_start > current:
            free_slots.append((current, busy_start))
        current = max(current, busy_end)
    if current < end:
        free_slots.append((current, end))
    return free_slots

# Get free slots for each participant within work hours but also considering Margaret's constraint for Tuesday.
margaret_free = get_free_slots(margaret_busy, work_start, work_end)
alexis_free = get_free_slots(alexis_busy, work_start, work_end)

# We further restrict the free slots for both to end before the latest_meeting_end
def restrict_slots(slots, limit):
    restricted = []
    for start, end in slots:
        slot_end = min(end, limit)
        if start < slot_end:
            restricted.append((start, slot_end))
    return restricted

margaret_free = restrict_slots(margaret_free, latest_meeting_end)
alexis_free = restrict_slots(alexis_free, latest_meeting_end)

def find_intersection_slot(slots1, slots2, duration):
    for s1, e1 in slots1:
        for s2, e2 in slots2:
            # Find the intersection of these two slots
            start = max(s1, s2)
            end = min(e1, e2)
            if end - start >= duration:
                return start, start + duration
    return None

meeting_time = find_intersection_slot(margaret_free, alexis_free, meeting_duration)

if meeting_time:
    start_time, end_time = meeting_time
    # Format the output in HH:MM:HH:MM and specify day as Tuesday
    output = f"Tuesday {start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}"
    print(output)
else:
    print("No available meeting slot satisfies all constraints.")