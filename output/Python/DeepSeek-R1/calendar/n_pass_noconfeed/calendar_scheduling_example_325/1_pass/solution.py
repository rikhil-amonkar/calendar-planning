def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def main():
    work_start_min = time_to_minutes("9:00")
    meeting_end_limit = time_to_minutes("15:30")
    meeting_duration = 30
    
    busy_intervals = []
    
    # Jose
    busy_intervals.append((time_to_minutes("11:00"), time_to_minutes("11:30")))
    busy_intervals.append((time_to_minutes("12:30"), time_to_minutes("13:00")))
    
    # Keith
    busy_intervals.append((time_to_minutes("14:00"), time_to_minutes("14:30")))
    busy_intervals.append((time_to_minutes("15:00"), time_to_minutes("15:30")))
    
    # Logan
    busy_intervals.append((time_to_minutes("9:00"), time_to_minutes("10:00")))
    busy_intervals.append((time_to_minutes("12:00"), time_to_minutes("12:30")))
    busy_intervals.append((time_to_minutes("15:00"), time_to_minutes("15:30")))
    
    # Megan
    busy_intervals.append((time_to_minutes("9:00"), time_to_minutes("10:30")))
    busy_intervals.append((time_to_minutes("11:00"), time_to_minutes("12:00")))
    busy_intervals.append((time_to_minutes("13:00"), time_to_minutes("13:30")))
    busy_intervals.append((time_to_minutes("14:30"), time_to_minutes("16:30")))
    
    # Gary
    busy_intervals.append((time_to_minutes("9:00"), time_to_minutes("9:30")))
    busy_intervals.append((time_to_minutes("10:00"), time_to_minutes("10:30")))
    busy_intervals.append((time_to_minutes("11:30"), time_to_minutes("13:00")))
    busy_intervals.append((time_to_minutes("13:30"), time_to_minutes("14:00")))
    busy_intervals.append((time_to_minutes("14:30"), time_to_minutes("16:30")))
    
    # Bobby
    busy_intervals.append((time_to_minutes("11:00"), time_to_minutes("11:30")))
    busy_intervals.append((time_to_minutes("12:00"), time_to_minutes("12:30")))
    busy_intervals.append((time_to_minutes("13:00"), time_to_minutes("16:00")))
    
    if not busy_intervals:
        merged = []
    else:
        sorted_intervals = sorted(busy_intervals, key=lambda x: x[0])
        merged = []
        current_start, current_end = sorted_intervals[0]
        for i in range(1, len(sorted_intervals)):
            interval = sorted_intervals[i]
            if interval[0] <= current_end:
                current_end = max(current_end, interval[1])
            else:
                merged.append((current_start, current_end))
                current_start, current_end = interval
        merged.append((current_start, current_end))
    
    gaps = []
    if not merged:
        gap_start = work_start_min
        gap_end = meeting_end_limit
        gaps.append((gap_start, gap_end))
    else:
        first_interval = merged[0]
        if first_interval[0] > work_start_min:
            gaps.append((work_start_min, first_interval[0]))
        
        for i in range(1, len(merged)):
            prev_end = merged[i-1][1]
            curr_start = merged[i][0]
            if curr_start > prev_end:
                gaps.append((prev_end, curr_start))
                
        last_interval = merged[-1]
        if last_interval[1] < meeting_end_limit:
            gaps.append((last_interval[1], meeting_end_limit))
    
    meeting_start = None
    for gap in gaps:
        s, e = gap
        available_end = min(e, meeting_end_limit)
        if s > meeting_end_limit - meeting_duration:
            continue
        if available_end - s >= meeting_duration:
            meeting_start = s
            break
    
    if meeting_start is None:
        print("No available slot found")
    else:
        meeting_end = meeting_start + meeting_duration
        start_str = minutes_to_time(meeting_start)
        end_str = minutes_to_time(meeting_end)
        print("Monday")
        print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()