def time_to_minutes(t):
    """Convert HH:MM to minutes from 00:00."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes from 00:00 to HH:MM."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def find_earliest_meeting(work_start, work_end, busy_slots, duration_minutes):
    """Find earliest meeting time within work hours avoiding busy slots."""
    # Convert work hours to minutes
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    
    # Sort busy slots and merge if needed (not required here as they're disjoint)
    free_slots = []
    current = work_start_min
    
    for start, end in busy_slots:
        start_min = time_to_minutes(start)
        end_min = time_to_minutes(end)
        if current < start_min:
            free_slots.append((current, start_min))
        current = max(current, end_min)
    
    if current < work_end_min:
        free_slots.append((current, work_end_min))
    
    # Find earliest slot of required duration
    for start, end in free_slots:
        if end - start >= duration_minutes:
            meeting_end = start + duration_minutes
            return start, meeting_end
    
    return None, None

def main():
    # Given data
    work_start = "09:00"
    work_end = "17:00"
    duration_minutes = 30
    
    # Samuel's busy times in HH:MM format
    samuel_busy = [
        ("09:00", "10:30"),
        ("11:30", "12:00"),
        ("13:00", "13:30"),
        ("14:00", "16:00"),
        ("16:30", "17:00")
    ]
    
    # Find earliest meeting time
    start_min, end_min = find_earliest_meeting(work_start, work_end, samuel_busy, duration_minutes)
    
    if start_min is None:
        print("No suitable time found.")
    else:
        start_time = minutes_to_time(start_min)
        end_time = minutes_to_time(end_min)
        print(f"{start_time}:{end_time}")
        print("Monday")

if __name__ == "__main__":
    main()