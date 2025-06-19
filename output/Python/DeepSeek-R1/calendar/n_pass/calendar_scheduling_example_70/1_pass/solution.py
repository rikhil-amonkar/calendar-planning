def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return (hour - 9) * 60 + minute

def minutes_to_time(total_minutes):
    hour = 9 + total_minutes // 60
    minute = total_minutes % 60
    return f"{hour:02d}:{minute:02d}"

def main():
    meeting_duration = 30  # minutes
    work_end_minutes = 8 * 60  # 17:00 is 8 hours after 9:00

    busy_intervals = []
    
    # Denise's busy intervals
    busy_intervals.append([time_to_minutes("12:00"), time_to_minutes("12:30")])
    busy_intervals.append([time_to_minutes("15:30"), time_to_minutes("16:00")])
    
    # Natalie's busy intervals
    busy_intervals.append([time_to_minutes("9:00"), time_to_minutes("11:30")])
    busy_intervals.append([time_to_minutes("12:00"), time_to_minutes("13:00")])
    busy_intervals.append([time_to_minutes("14:00"), time_to_minutes("14:30")])
    busy_intervals.append([time_to_minutes("15:00"), time_to_minutes("17:00")])
    
    # Angela has no meetings, so no intervals to add
    
    if busy_intervals:
        busy_intervals.sort(key=lambda x: x[0])
        merged = []
        start, end = busy_intervals[0]
        for i in range(1, len(busy_intervals)):
            s, e = busy_intervals[i]
            if s <= end:
                end = max(end, e)
            else:
                merged.append([start, end])
                start, end = s, e
        merged.append([start, end])
    else:
        merged = []
    
    free_intervals = []
    current = 0
    for interval in merged:
        s, e = interval
        if current < s:
            free_intervals.append([current, s])
        current = e
    if current < work_end_minutes:
        free_intervals.append([current, work_end_minutes])
    
    meeting_time = None
    for interval in free_intervals:
        start_min, end_min = interval
        if end_min - start_min >= meeting_duration:
            meeting_start = start_min
            meeting_end = start_min + meeting_duration
            meeting_time = (meeting_start, meeting_end)
            break
    
    if meeting_time is None:
        print("No suitable time found")
    else:
        start_str = minutes_to_time(meeting_time[0])
        end_str = minutes_to_time(meeting_time[1])
        time_range_str = f"{start_str}:{end_str}"
        print("Monday")
        print(time_range_str)

if __name__ == "__main__":
    main()