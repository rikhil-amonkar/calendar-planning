from datetime import datetime, timedelta

def parse_time(time_str):
    """Convert 'HH:MM' to minutes since midnight."""
    return datetime.strptime(time_str, "%H:%M")

def time_to_minutes(t):
    return t.hour * 60 + t.minute

def minutes_to_str(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def busy_intervals_to_minute_ranges(busy_list, day):
    """Convert busy intervals like '9:00 to 10:30' to (start_minute, end_minute)."""
    ranges = []
    for interval in busy_list:
        start_str, end_str = interval.split(" to ")
        start_min = time_to_minutes(parse_time(start_str))
        end_min = time_to_minutes(parse_time(end_str))
        ranges.append((start_min, end_min))
    return ranges

def is_free(person_busy, start_min, end_min):
    for bs, be in person_busy:
        if not (end_min <= bs or start_min >= be):
            return False
    return True

def main():
    # Work hours
    work_start = time_to_minutes(parse_time("9:00"))
    work_end = time_to_minutes(parse_time("17:00"))
    
    # Amanda's busy times (Tuesday only for our filtered search)
    amanda_busy_tuesday = [
        ("9:00", "9:30"),
        ("10:00", "10:30"),
        ("11:30", "12:00"),
        ("13:30", "14:30"),
        ("15:30", "16:00"),
        ("16:30", "17:00"),
    ]
    
    nathan_busy_tuesday = [
        ("9:00", "10:30"),
        ("11:00", "13:00"),
        ("13:30", "14:00"),
        ("14:30", "15:30"),
        ("16:00", "16:30"),
    ]
    
    # Convert to minutes
    amanda_busy_min = busy_intervals_to_minute_ranges(amanda_busy_tuesday, "Tuesday")
    nathan_busy_min = busy_intervals_to_minute_ranges(nathan_busy_tuesday, "Tuesday")
    
    meeting_duration = 30  # minutes
    
    # Only Tuesday allowed (Nathan constraint)
    # Amanda doesn't want Tuesday after 11:00 -> meeting must end by 11:00 or start before 11:00 and end at/before 11:00.
    # Let's interpret as: meeting start time must be < 11:00 and end time <= 11:00.
    # To be safe, we'll only allow start times where start + duration <= 11:00*60 minutes.
    amanda_max_end = time_to_minutes(parse_time("11:00"))
    
    found_slot = None
    
    for start_min in range(work_start, work_end - meeting_duration + 1, 30):
        end_min = start_min + meeting_duration
        
        # Amanda's Tuesday after 11:00 constraint
        if end_min > amanda_max_end:
            continue
        
        if is_free(amanda_busy_min, start_min, end_min) and is_free(nathan_busy_min, start_min, end_min):
            found_slot = ("Tuesday", start_min, end_min)
            break
    
    if found_slot:
        day, start_min, end_min = found_slot
        print(f"{day}:{minutes_to_str(start_min)}:{minutes_to_str(end_min)}")
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()