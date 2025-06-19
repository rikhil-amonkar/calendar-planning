def main():
    # Total minutes from 9:00 to 17:00 (8 hours)
    total_minutes = 480
    meeting_duration = 30
    
    # Define busy intervals for each participant (start_minute, end_minute) relative to 9:00
    daniel = []
    kathleen = [(330, 390)]   # 14:30 to 15:30
    carolyn = [(180, 210), (240, 270)]   # 12:00-12:30, 13:00-13:30
    roger = []
    cheryl = [(0, 30), (60, 150), (210, 270), (300, 480)]
    virginia = [(30, 150), (180, 210), (240, 270), (330, 390), (420, 480)]
    angela = [(30, 60), (90, 150), (180, 210), (240, 270), (300, 450)]
    
    # Combine all busy intervals
    all_busy = daniel + kathleen + carolyn + roger + cheryl + virginia + angela
    
    # Initialize array for group availability: False means free
    group_busy = [False] * total_minutes
    
    # Mark busy intervals in the group_busy array
    for start, end in all_busy:
        end = min(end, total_minutes)
        for minute in range(start, end):
            if minute < total_minutes:
                group_busy[minute] = True
    
    # Search for a 30-minute slot starting from 12:30 (210 minutes) onwards
    start_time = None
    for start in range(210, total_minutes - meeting_duration + 1):
        # Check if the next 'meeting_duration' minutes are free
        if not any(group_busy[start:start+meeting_duration]):
            start_time = start
            break
    
    # Convert minutes back to time string
    def minutes_to_time(m):
        hour = 9 + m // 60
        minute = m % 60
        return f"{hour}:{minute:02d}"
    
    if start_time is None:
        print("No suitable time found")
    else:
        start_str = minutes_to_time(start_time)
        end_str = minutes_to_time(start_time + meeting_duration)
        print("Monday")
        print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()