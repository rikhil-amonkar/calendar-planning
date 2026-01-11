def time_to_minutes(t):
    """Convert HH:MM to minutes from 00:00"""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes from 00:00 to HH:MM"""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Work hours
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    day_length = work_end - work_start  # 480 minutes
    
    # Busy count per minute from 9:00 (index 0 = 9:00, index 479 = 16:59)
    busy_count = [0] * day_length
    
    # Blocked intervals for each person (in HH:MM format, relative to real clock)
    blocked_intervals = [
        # Doris
        [("9:00", "11:00"), ("13:30", "14:00"), ("16:00", "16:30")],
        # Theresa
        [("10:00", "12:00")],
        # Christian (none)
        [],
        # Terry
        [("9:30", "10:00"), ("11:30", "12:00"), ("12:30", "13:00"),
         ("13:30", "14:00"), ("14:30", "15:00"), ("15:30", "17:00")],
        # Carolyn
        [("9:00", "10:30"), ("11:00", "11:30"), ("12:00", "13:00"),
         ("13:30", "14:30"), ("15:00", "17:00")],
        # Kyle
        [("9:00", "9:30"), ("11:30", "12:00"), ("12:30", "13:00"),
         ("14:30", "17:00")]
    ]
    
    # Mark busy minutes
    for person_blocks in blocked_intervals:
        for start_str, end_str in person_blocks:
            start = time_to_minutes(start_str) - work_start
            end = time_to_minutes(end_str) - work_start
            # Clamp to work hours
            start = max(start, 0)
            end = min(end, day_length)
            for minute in range(start, end):
                if 0 <= minute < day_length:
                    busy_count[minute] += 1
    
    # Find first 30 consecutive minutes with busy_count == 0
    meeting_duration = 30
    for start_minute in range(day_length - meeting_duration + 1):
        if all(busy_count[start_minute + i] == 0 for i in range(meeting_duration)):
            # Found slot
            meeting_start_abs = work_start + start_minute
            meeting_end_abs = meeting_start_abs + meeting_duration
            print(f"{minutes_to_time(meeting_start_abs)}:{minutes_to_time(meeting_end_abs)}")
            print("Monday")
            return
    
    print("No slot found")

if __name__ == "__main__":
    main()