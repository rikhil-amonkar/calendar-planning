from datetime import datetime, timedelta

def time_to_minutes(t):
    """Convert 'HH:MM' to minutes from 00:00."""
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes from 00:00 to 'HH:MM'."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def find_meeting_slot():
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    duration = 30
    
    # Busy times in minutes from 00:00
    shirley_busy = [
        ("Monday", "10:30", "11:00"),
        ("Monday", "12:00", "12:30"),
        ("Monday", "16:00", "16:30"),
        ("Tuesday", "09:30", "10:00")
    ]
    
    albert_busy = [
        ("Monday", "09:00", "17:00"),
        ("Tuesday", "09:30", "11:00"),
        ("Tuesday", "11:30", "12:30"),
        ("Tuesday", "13:00", "16:00"),
        ("Tuesday", "16:30", "17:00")
    ]
    
    days = ["Monday", "Tuesday"]
    
    for day in days:
        # Collect busy intervals for this day
        shirley_intervals = []
        albert_intervals = []
        
        for d, start, end in shirley_busy:
            if d == day:
                shirley_intervals.append((time_to_minutes(start), time_to_minutes(end)))
        
        for d, start, end in albert_busy:
            if d == day:
                albert_intervals.append((time_to_minutes(start), time_to_minutes(end)))
        
        # Generate free intervals for each person within work hours
        def free_intervals(busy_intervals, day_start, day_end):
            busy_intervals.sort()
            free = []
            current_start = day_start
            
            for start_busy, end_busy in busy_intervals:
                if current_start < start_busy:
                    free.append((current_start, start_busy))
                current_start = max(current_start, end_busy)
            
            if current_start < day_end:
                free.append((current_start, day_end))
            return free
        
        shirley_free = free_intervals(shirley_intervals, work_start, work_end)
        albert_free = free_intervals(albert_intervals, work_start, work_end)
        
        # Find overlapping free slots of at least 'duration' minutes
        for s_start, s_end in shirley_free:
            for a_start, a_end in albert_free:
                overlap_start = max(s_start, a_start)
                overlap_end = min(s_end, a_end)
                if overlap_end - overlap_start >= duration:
                    # Found a slot
                    if day == "Tuesday" and overlap_start >= time_to_minutes("10:30"):
                        # Less preferred, but still valid. We'll take earliest possible.
                        # For now, continue to find earliest overall.
                        pass
                    # Return earliest possible slot
                    slot_end = overlap_start + duration
                    time_str = f"{minutes_to_time(overlap_start)}:{minutes_to_time(slot_end)}"
                    return day, time_str
    
    return None, None

day, time_range = find_meeting_slot()
if day and time_range:
    start_time, end_time = time_range.split(':')
    print(f"{day} {start_time}:{end_time}")
else:
    print("No suitable slot found")