from datetime import datetime, timedelta

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Define work day boundaries in minutes (9:00 to 17:00)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# Duration of the meeting in minutes
meeting_duration = 30

# Define the busy intervals for each person in minutes on each day.
# For each interval, we represent it as a tuple (start, end) where times are in minutes.
# Jesse's busy schedule:
jesse_busy = {
    "Monday": [(time_to_minutes("13:30"), time_to_minutes("14:00")),
               (time_to_minutes("14:30"), time_to_minutes("15:00"))],
    "Tuesday": [(time_to_minutes("09:00"), time_to_minutes("09:30")),
                (time_to_minutes("13:00"), time_to_minutes("13:30")),
                (time_to_minutes("14:00"), time_to_minutes("15:00"))]
}

# Lawrence's busy schedule:
lawrence_busy = {
    "Monday": [(time_to_minutes("09:00"), time_to_minutes("17:00"))],  # busy whole day
    "Tuesday": [(time_to_minutes("09:30"), time_to_minutes("10:30")),
                (time_to_minutes("11:30"), time_to_minutes("12:30")),
                (time_to_minutes("13:00"), time_to_minutes("13:30")),
                (time_to_minutes("14:30"), time_to_minutes("15:00")),
                (time_to_minutes("15:30"), time_to_minutes("16:30"))]
}
# Additional constraint: Lawrence cannot meet on Tuesday after 16:30,
# meaning the meeting must finish by 16:30; hence the meeting must start no later than 16:00.
max_meeting_start = time_to_minutes("16:00")

def get_free_slots(busy, day):
    """Return available free slots within the work day for a given day's busy intervals."""
    free = []
    busy_sorted = sorted(busy.get(day, []))
    current_start = work_start
    for interval in busy_sorted:
        b_start, b_end = interval
        if current_start < b_start:
            free.append((current_start, b_start))
        current_start = max(current_start, b_end)
    if current_start < work_end:
        free.append((current_start, work_end))
    return free

def intersect_slots(slots1, slots2):
    """Return intersection of two lists of slots."""
    intersections = []
    i, j = 0, 0
    while i < len(slots1) and j < len(slots2):
        start1, end1 = slots1[i]
        start2, end2 = slots2[j]
        start = max(start1, start2)
        end = min(end1, end2)
        if start + meeting_duration <= end:  # enough room for the meeting
            intersections.append((start, end))
        # Move the pointer which ends first
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

# Try scheduling on Monday and Tuesday (Monday for Lawrence is entirely busy, so Tuesday is our only option)
chosen_day = None
chosen_start = None

for day in ["Monday", "Tuesday"]:
    # Get free slots for both participants
    jesse_free = get_free_slots(jesse_busy, day)
    lawrence_free = get_free_slots(lawrence_busy, day)
    # If it's Tuesday, honor Lawrence's extra constraint: meeting must start before or at 16:00.
    if day == "Tuesday":
        lawrence_free = [(s, min(e, time_to_minutes("16:30"))) for s,e in lawrence_free if s <= max_meeting_start]
    
    # Find intersections of free slots between Jesse and Lawrence
    common_slots = intersect_slots(jesse_free, lawrence_free)
    for slot in common_slots:
        slot_start, slot_end = slot
        # Ensure meeting can be scheduled starting at slot_start within the slot and any extra constraints.
        if day == "Tuesday" and slot_start > max_meeting_start:
            continue
        # Choose the earliest possible time that can accommodate the meeting.
        chosen_day = day
        chosen_start = slot_start
        break
    if chosen_day:
        break

if chosen_day and chosen_start is not None:
    meeting_start = chosen_start
    meeting_end = meeting_start + meeting_duration
    meeting_time_str = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    print(f"{chosen_day} {meeting_time_str}")
else:
    print("No available meeting time could be found.")