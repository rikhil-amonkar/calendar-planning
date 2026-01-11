def time_to_minutes(t):
    """Convert 'HH:MM' to minutes since midnight."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes since midnight to 'HH:MM'."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def schedule_meeting(participants_busy, day, work_start, work_end, duration_minutes):
    """
    participants_busy: list of list of (start, end) in 'HH:MM' format
    work_start, work_end: 'HH:MM'
    duration_minutes: int
    Returns (day, start_time, end_time) or None
    """
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    
    # Convert all busy times to minutes
    busy_minutes = []
    for person in participants_busy:
        person_busy = []
        for s, e in person:
            person_busy.append((time_to_minutes(s), time_to_minutes(e)))
        busy_minutes.append(person_busy)
    
    # Check each possible start time from work_start to work_end - duration
    for start in range(work_start_min, work_end_min - duration_minutes + 1, 30):
        end = start + duration_minutes
        # Check if this slot overlaps with any busy period for any participant
        conflict = False
        for person_busy in busy_minutes:
            for bs, be in person_busy:
                if not (end <= bs or start >= be):  # overlap exists
                    conflict = True
                    break
            if conflict:
                break
        if not conflict:
            return day, minutes_to_time(start), minutes_to_time(end)
    return None

# Define the busy times for each participant (HH:MM format)
participants_busy = [
    [("09:30", "10:00"), ("10:30", "11:00")],  # Joe
    [("11:30", "12:00"), ("15:00", "15:30")],  # Keith
    [("09:00", "09:30"), ("13:00", "13:30")],  # Patricia
    [("09:00", "11:00"), ("11:30", "16:30")],  # Nancy
    [("09:00", "10:00"), ("10:30", "11:00"), ("11:30", "12:30"), 
     ("13:00", "14:00"), ("14:30", "15:00"), ("15:30", "16:00"), 
     ("16:30", "17:00")]  # Pamela
]

day = "Monday"
work_start = "09:00"
work_end = "17:00"
duration = 30

result = schedule_meeting(participants_busy, day, work_start, work_end, duration)

if result:
    day, start, end = result
    print(f"{day}: {start}:{end}")
else:
    print("No suitable slot found.")