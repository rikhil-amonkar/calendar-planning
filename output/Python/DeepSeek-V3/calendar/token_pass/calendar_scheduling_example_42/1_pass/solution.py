def time_to_minutes(t):
    """Convert HH:MM to minutes from midnight."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes from midnight to HH:MM."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def schedule_meeting(work_start, work_end, busy_slots, duration_minutes):
    """
    work_start, work_end: 'HH:MM'
    busy_slots: list of list of tuples for each person: [(start1, end1), ...] in 'HH:MM'
    duration_minutes: int
    returns (day, start_time, end_time) or None
    """
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    
    # Start with whole work range as free for common
    common_free = [(work_start_min, work_end_min)]
    
    for person_busy in busy_slots:
        # Convert person's busy slots to minutes
        busy_min = [(time_to_minutes(s), time_to_minutes(e)) for s, e in person_busy]
        busy_min.sort()
        
        # Subtract busy from current common_free
        new_common_free = []
        for free_start, free_end in common_free:
            current_start = free_start
            for bs, be in busy_min:
                if be <= current_start:
                    continue
                if bs >= free_end:
                    break
                if bs > current_start:
                    new_common_free.append((current_start, bs))
                current_start = max(current_start, be)
            if current_start < free_end:
                new_common_free.append((current_start, free_end))
        common_free = new_common_free
    
    # Find a slot of at least duration_minutes
    for start, end in common_free:
        if end - start >= duration_minutes:
            return start, start + duration_minutes
    return None

# Define the problem
work_start = "09:00"
work_end = "17:00"
duration = 60  # minutes

# Busy slots for each person: list of (start, end) as strings
julie_busy = [("09:00", "09:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:30", "14:00"), ("16:00", "17:00")]
sean_busy = [("09:00", "09:30"), ("13:00", "13:30"), ("15:00", "15:30"), ("16:00", "16:30")]
lori_busy = [("10:00", "10:30"), ("11:00", "13:00"), ("15:30", "17:00")]

busy_slots = [julie_busy, sean_busy, lori_busy]

result = schedule_meeting(work_start, work_end, busy_slots, duration)

if result:
    start_min, end_min = result
    start_time = minutes_to_time(start_min)
    end_time = minutes_to_time(end_min)
    print(f"Monday {start_time}:{end_time}")
else:
    print("No suitable slot found")