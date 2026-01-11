def time_to_minutes(t):
    """Convert HH:MM to minutes from 00:00"""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes from 00:00 to HH:MM"""
    return f"{m // 60:02d}:{m % 60:02d}"

def busy_to_free(busy_intervals, day_start_min, day_end_min, duration):
    """
    busy_intervals: list of (start_min, end_min) within day in minutes from 00:00
    day_start_min, day_end_min: work hours in minutes from 00:00
    duration: meeting duration in minutes
    Returns list of (free_start, free_end) in minutes from 00:00
    """
    # Sort busy intervals
    busy = sorted(busy_intervals)
    free = []
    
    # Before first busy
    current_time = day_start_min
    for start, end in busy:
        if start > current_time:
            free.append((current_time, start))
        current_time = max(current_time, end)
    
    # After last busy
    if current_time < day_end_min:
        free.append((current_time, day_end_min))
    
    # Filter by duration
    return [(s, e) for s, e in free if e - s >= duration]

def parse_schedule(schedule_str, day_offset_min):
    """
    schedule_str: e.g., "Monday during 14:30 to 15:00, Tuesday during 9:00 to 11:30"
    day_offset_min: minutes from 00:00 for the start of that day's work hours (9:00)
    Returns list of (start_min, end_min) in absolute minutes from 00:00 Monday 00:00? 
    Actually simpler: treat each day separately, so day_offset_min is day start in minutes from 00:00.
    But busy times given in HH:MM local time, so convert to minutes from 00:00 directly.
    Wait careful: 14:30 is 14:30 on that day, so minutes from 00:00 that day = time_to_minutes("14:30").
    We'll keep day separate, so pass day index.
    """
    # Actually, let's handle parsing outside this function for clarity.
    pass

def main():
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    duration = 30
    
    # Bobby's schedule
    bobby_busy = {
        "Monday": [
            ("14:30", "15:00"),
        ],
        "Tuesday": [
            ("9:00", "11:30"),
            ("12:00", "12:30"),
            ("13:00", "15:00"),
            ("15:30", "17:00"),
        ]
    }
    
    # Michael's schedule
    michael_busy = {
        "Monday": [
            ("9:00", "10:00"),
            ("10:30", "13:30"),
            ("14:00", "15:00"),
            ("15:30", "17:00"),
        ],
        "Tuesday": [
            ("9:00", "10:30"),
            ("11:00", "11:30"),
            ("12:00", "14:00"),
            ("15:00", "16:00"),
            ("16:30", "17:00"),
        ]
    }
    
    days = ["Monday", "Tuesday"]
    
    for day in days:
        # Convert busy times to minutes from 00:00
        bobby_busy_min = [(time_to_minutes(s), time_to_minutes(e)) for s, e in bobby_busy.get(day, [])]
        michael_busy_min = [(time_to_minutes(s), time_to_minutes(e)) for s, e in michael_busy.get(day, [])]
        
        # Get free slots for each
        bobby_free = busy_to_free(bobby_busy_min, work_start, work_end, duration)
        michael_free = busy_to_free(michael_busy_min, work_start, work_end, duration)
        
        # Intersect free slots
        i, j = 0, 0
        while i < len(bobby_free) and j < len(michael_free):
            s1, e1 = bobby_free[i]
            s2, e2 = michael_free[j]
            
            intersect_start = max(s1, s2)
            intersect_end = min(e1, e2)
            
            if intersect_end - intersect_start >= duration:
                # Found a slot
                print(f"{day}:{minutes_to_time(intersect_start)}:{minutes_to_time(intersect_start + duration)}")
                return
            
            # Move the one that ends earlier
            if e1 < e2:
                i += 1
            else:
                j += 1
    
    print("No slot found")

if __name__ == "__main__":
    main()