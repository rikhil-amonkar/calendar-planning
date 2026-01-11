def time_to_minutes(t):
    """Convert HH:MM to minutes from midnight."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes from midnight to HH:MM."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def find_meeting_time(work_start, work_end, duration, schedules, day):
    """
    work_start, work_end: "HH:MM"
    duration: minutes
    schedules: list of list of (busy_start, busy_end) in "HH:MM" format for each person
    day: string day name
    """
    work_s = time_to_minutes(work_start)
    work_e = time_to_minutes(work_end)
    
    # Combine all busy intervals from all participants
    busy_intervals = []
    for person_schedule in schedules:
        for start, end in person_schedule:
            busy_intervals.append((time_to_minutes(start), time_to_minutes(end)))
    
    # Sort by start time
    busy_intervals.sort()
    
    # Merge overlapping busy intervals
    merged = []
    for start, end in busy_intervals:
        if not merged or start > merged[-1][1]:
            merged.append([start, end])
        else:
            merged[-1][1] = max(merged[-1][1], end)
    
    # Find free slots within work hours
    free_slots = []
    current_start = work_s
    
    for start, end in merged:
        if start > current_start:
            free_slots.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < work_e:
        free_slots.append((current_start, work_e))
    
    # Find earliest slot with enough duration
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= duration:
            meeting_start = slot_start
            meeting_end = meeting_start + duration
            return day, minutes_to_time(meeting_start), minutes_to_time(meeting_end)
    
    return None

# Define the problem
work_start = "09:00"
work_end = "17:00"
duration = 30
day = "Monday"

adam_schedule = [
    ("09:30", "10:00"),
    ("12:30", "13:00"),
    ("14:30", "15:00"),
    ("16:30", "17:00")
]

roy_schedule = [
    ("10:00", "11:00"),
    ("11:30", "13:00"),
    ("13:30", "14:30"),
    ("16:30", "17:00")
]

schedules = [adam_schedule, roy_schedule]

# Find meeting time
result = find_meeting_time(work_start, work_end, duration, schedules, day)

if result:
    day, start, end = result
    print(f"{day}:{start}:{end}")
else:
    print("No suitable time found.")