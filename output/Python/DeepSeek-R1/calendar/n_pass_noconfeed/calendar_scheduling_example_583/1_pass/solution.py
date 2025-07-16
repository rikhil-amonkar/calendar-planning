def time_to_minutes(time_str):
    hour, minute = map(int, time_str.split(':'))
    return (hour - 9) * 60 + minute

def minutes_to_time(minutes):
    total_minutes = minutes
    hour = 9 + total_minutes // 60
    minute = total_minutes % 60
    return hour, minute

def main():
    # Define busy intervals for Lisa and Anthony
    lisa_busy = [
        ("9:00", "9:30"),
        ("10:30", "11:00"),
        ("14:00", "16:00")
    ]
    anthony_busy = [
        ("9:00", "9:30"),
        ("11:00", "11:30"),
        ("12:30", "13:30"),
        ("14:00", "15:00"),
        ("15:30", "16:00"),
        ("16:30", "17:00")
    ]
    
    # Convert intervals to minutes since 9:00
    busy_intervals = []
    for start, end in lisa_busy:
        start_min = time_to_minutes(start)
        end_min = time_to_minutes(end)
        busy_intervals.append([start_min, end_min])
    for start, end in anthony_busy:
        start_min = time_to_minutes(start)
        end_min = time_to_minutes(end)
        busy_intervals.append([start_min, end_min])
    
    # Sort and merge busy intervals
    busy_intervals.sort(key=lambda x: x[0])
    merged = []
    start_curr, end_curr = busy_intervals[0]
    for i in range(1, len(busy_intervals)):
        s, e = busy_intervals[i]
        if s <= end_curr:
            end_curr = max(end_curr, e)
        else:
            merged.append([start_curr, end_curr])
            start_curr, end_curr = s, e
    merged.append([start_curr, end_curr])
    
    # Find free intervals within 9:00-17:00 (0 to 480 minutes)
    free_intervals = []
    current = 0
    for interval in merged:
        s, e = interval
        if current < s:
            free_intervals.append([current, s])
        current = e
    if current < 480:
        free_intervals.append([current, 480])
    
    # Find the earliest 30-minute slot
    meeting_start = None
    for interval in free_intervals:
        start, end = interval
        if end - start >= 30:
            meeting_start = start
            break
    
    # Convert meeting time to HH:MM format
    start_hour, start_min = minutes_to_time(meeting_start)
    end_hour, end_min = minutes_to_time(meeting_start + 30)
    
    # Format the output
    time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
    print("Monday")
    print(time_str)

if __name__ == "__main__":
    main()