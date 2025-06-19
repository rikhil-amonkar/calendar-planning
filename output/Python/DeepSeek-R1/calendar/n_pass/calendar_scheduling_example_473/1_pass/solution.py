def parse_time(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def main():
    work_start = parse_time("9:00")
    work_end = parse_time("17:00")
    meeting_duration = 30

    busy_intervals = []
    
    # Gregory
    busy_intervals.append((parse_time("9:00"), parse_time("9:30")))
    busy_intervals.append((parse_time("11:30"), parse_time("12:00")))
    
    # Jonathan
    busy_intervals.append((parse_time("9:00"), parse_time("9:30")))
    busy_intervals.append((parse_time("12:00"), parse_time("12:30")))
    busy_intervals.append((parse_time("13:00"), parse_time("13:30")))
    busy_intervals.append((parse_time("15:00"), parse_time("16:00")))
    busy_intervals.append((parse_time("16:30"), parse_time("17:00")))
    
    # Barbara
    busy_intervals.append((parse_time("10:00"), parse_time("10:30")))
    busy_intervals.append((parse_time("13:30"), parse_time("14:00")))
    
    # Jesse
    busy_intervals.append((parse_time("10:00"), parse_time("11:00")))
    busy_intervals.append((parse_time("12:30"), parse_time("14:30")))
    
    # Alan
    busy_intervals.append((parse_time("9:30"), parse_time("11:00")))
    busy_intervals.append((parse_time("11:30"), parse_time("12:30")))
    busy_intervals.append((parse_time("13:00"), parse_time("15:30")))
    busy_intervals.append((parse_time("16:00"), parse_time("17:00")))
    
    # Nicole
    busy_intervals.append((parse_time("9:00"), parse_time("10:30")))
    busy_intervals.append((parse_time("11:30"), parse_time("12:00")))
    busy_intervals.append((parse_time("12:30"), parse_time("13:30")))
    busy_intervals.append((parse_time("14:00"), parse_time("17:00")))
    
    # Catherine
    busy_intervals.append((parse_time("9:00"), parse_time("10:30")))
    busy_intervals.append((parse_time("12:00"), parse_time("13:30")))
    busy_intervals.append((parse_time("15:00"), parse_time("15:30")))
    busy_intervals.append((parse_time("16:00"), parse_time("16:30")))
    
    if not busy_intervals:
        free_interval = (work_start, work_end)
        if free_interval[1] - free_interval[0] >= meeting_duration:
            meeting_start = free_interval[0]
            meeting_end = meeting_start + meeting_duration
            start_str = format_time(meeting_start)
            end_str = format_time(meeting_end)
            print(f"Monday {start_str}:{end_str}")
            return
    
    busy_intervals.sort(key=lambda x: x[0])
    merged = []
    current_start, current_end = busy_intervals[0]
    for i in range(1, len(busy_intervals)):
        s, e = busy_intervals[i]
        if s <= current_end:
            if e > current_end:
                current_end = e
        else:
            merged.append((current_start, current_end))
            current_start, current_end = s, e
    merged.append((current_start, current_end))
    
    free_intervals = []
    current = work_start
    for start, end in merged:
        if current < start:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))
    
    meeting_time = None
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_time = (start, start + meeting_duration)
            break
    
    if meeting_time:
        start_str = format_time(meeting_time[0])
        end_str = format_time(meeting_time[1])
        print(f"Monday {start_str}:{end_str}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()