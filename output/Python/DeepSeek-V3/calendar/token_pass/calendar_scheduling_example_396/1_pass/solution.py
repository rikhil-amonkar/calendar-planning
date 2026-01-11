def time_to_minutes(t):
    """Convert 'HH:MM' to minutes from 00:00."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes from 00:00 to 'HH:MM'."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def find_meeting_slot(busy_intervals, work_start, work_end, duration):
    """
    busy_intervals: list of (start, end) in minutes from 00:00
    work_start, work_end: minutes from 00:00
    duration: minutes
    Returns (start, end) in minutes from 00:00 or None
    """
    # Merge busy intervals
    if not busy_intervals:
        return (work_start, work_start + duration)
    
    busy_intervals.sort()
    merged = []
    current_start, current_end = busy_intervals[0]
    
    for start, end in busy_intervals[1:]:
        if start <= current_end:
            current_end = max(current_end, end)
        else:
            merged.append((current_start, current_end))
            current_start, current_end = start, end
    merged.append((current_start, current_end))
    
    # Look for gaps within work hours
    prev_end = work_start
    for start, end in merged:
        if start > prev_end and start - prev_end >= duration:
            return (prev_end, prev_end + duration)
        prev_end = max(prev_end, end)
    
    if work_end - prev_end >= duration:
        return (prev_end, prev_end + duration)
    
    return None

def main():
    # Work hours 9:00 to 17:00
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    duration = 30  # minutes
    
    # Busy times in HH:MM format (converted to minutes from 00:00)
    # Andrea: free all day → no busy intervals
    # Jack: 9:00-9:30, 14:00-14:30
    # Madison: 9:30-10:30, 13:00-14:00, 15:00-15:30, 16:30-17:00
    # Rachel: 9:30-10:30, 11:00-11:30, 12:00-13:30, 14:30-15:30, 16:00-17:00
    # Douglas: 9:00-11:30, 12:00-16:30
    # Ryan: 9:00-9:30, 13:00-14:00, 14:30-17:00
    
    busy_times = [
        # Jack
        ("09:00", "09:30"),
        ("14:00", "14:30"),
        # Madison
        ("09:30", "10:30"),
        ("13:00", "14:00"),
        ("15:00", "15:30"),
        ("16:30", "17:00"),
        # Rachel
        ("09:30", "10:30"),
        ("11:00", "11:30"),
        ("12:00", "13:30"),
        ("14:30", "15:30"),
        ("16:00", "17:00"),
        # Douglas
        ("09:00", "11:30"),
        ("12:00", "16:30"),
        # Ryan
        ("09:00", "09:30"),
        ("13:00", "14:00"),
        ("14:30", "17:00"),
    ]
    
    # Convert to minutes from 00:00
    busy_intervals = [(time_to_minutes(s), time_to_minutes(e)) for s, e in busy_times]
    
    slot = find_meeting_slot(busy_intervals, work_start, work_end, duration)
    
    if slot:
        start_min, end_min = slot
        start_time = minutes_to_time(start_min)
        end_time = minutes_to_time(end_min)
        print(f"Monday\n{start_time}:{end_time}")
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()