from datetime import datetime, timedelta

def time_to_minutes(t):
    """Convert 'HH:MM' to minutes since midnight."""
    return t.hour * 60 + t.minute

def minutes_to_time(m):
    """Convert minutes since midnight to 'HH:MM' string."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def find_meeting_time(eric_busy, henry_busy, work_start, work_end, duration, preference_cutoff=None):
    # Convert work hours to minutes
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    
    # Generate free slots for Eric
    eric_free = []
    current = work_start_min
    for start, end in sorted(eric_busy):
        s = time_to_minutes(start)
        e = time_to_minutes(end)
        if current < s:
            eric_free.append((current, s))
        current = max(current, e)
    if current < work_end_min:
        eric_free.append((current, work_end_min))
    
    # Generate free slots for Henry
    henry_free = []
    current = work_start_min
    for start, end in sorted(henry_busy):
        s = time_to_minutes(start)
        e = time_to_minutes(end)
        if current < s:
            henry_free.append((current, s))
        current = max(current, e)
    if current < work_end_min:
        henry_free.append((current, work_end_min))
    
    # Find overlaps of at least duration minutes
    overlaps = []
    for e_start, e_end in eric_free:
        for h_start, h_end in henry_free:
            overlap_start = max(e_start, h_start)
            overlap_end = min(e_end, h_end)
            if overlap_end - overlap_start >= duration:
                overlaps.append((overlap_start, overlap_end))
    
    # Sort by start time
    overlaps.sort(key=lambda x: x[0])
    
    # Apply preference: earliest slot that starts <= preference_cutoff if possible
    chosen = None
    if preference_cutoff is not None:
        pref_cutoff_min = time_to_minutes(preference_cutoff)
        for start, end in overlaps:
            if start <= pref_cutoff_min:
                chosen = (start, start + duration)
                break
    if chosen is None and overlaps:
        chosen = (overlaps[0][0], overlaps[0][0] + duration)
    
    return chosen

# Input data
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
duration = 30  # minutes

eric_busy = [
    (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
    (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:00", "%H:%M"))
]

henry_busy = [
    (datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
    (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
    (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
    (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
    (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
    (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
]

# Henry's preference: rather not meet after 10:00, so try to pick a slot starting <= 10:00
preference_cutoff = datetime.strptime("10:00", "%H:%M")

chosen_slot = find_meeting_time(eric_busy, henry_busy, work_start, work_end, duration, preference_cutoff)

if chosen_slot:
    start_time = minutes_to_time(chosen_slot[0])
    end_time = minutes_to_time(chosen_slot[1])
    print(f"Monday {start_time}:{end_time}")
else:
    print("No suitable time found.")