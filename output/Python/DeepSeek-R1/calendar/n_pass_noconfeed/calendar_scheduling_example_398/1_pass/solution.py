def time_to_minutes(time_str):
    h, m = time_str.split(':')
    return (int(h) - 9) * 60 + int(m)

def minutes_to_time(minutes):
    total_minutes_abs = 9 * 60 + minutes
    h = total_minutes_abs // 60
    m = total_minutes_abs % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Work day: 9:00 to 17:00 -> 0 to 480 minutes
    work_start = 0
    work_end = 480
    meeting_duration = 30
    
    # List to collect all busy intervals
    busy_intervals = []
    
    # Doris
    busy_intervals.append((time_to_minutes("9:00"), time_to_minutes("11:00")))
    busy_intervals.append((time_to_minutes("13:30"), time_to_minutes("14:00")))
    busy_intervals.append((time_to_minutes("16:00"), time_to_minutes("16:30")))
    
    # Theresa
    busy_intervals.append((time_to_minutes("10:00"), time_to_minutes("12:00")))
    
    # Terry
    busy_intervals.append((time_to_minutes("9:30"), time_to_minutes("10:00")))
    busy_intervals.append((time_to_minutes("11:30"), time_to_minutes("12:00")))
    busy_intervals.append((time_to_minutes("12:30"), time_to_minutes("13:00")))
    busy_intervals.append((time_to_minutes("13:30"), time_to_minutes("14:00")))
    busy_intervals.append((time_to_minutes("14:30"), time_to_minutes("15:00")))
    busy_intervals.append((time_to_minutes("15:30"), time_to_minutes("17:00")))
    
    # Carolyn
    busy_intervals.append((time_to_minutes("9:00"), time_to_minutes("10:30")))
    busy_intervals.append((time_to_minutes("11:00"), time_to_minutes("11:30")))
    busy_intervals.append((time_to_minutes("12:00"), time_to_minutes("13:00")))
    busy_intervals.append((time_to_minutes("13:30"), time_to_minutes("14:30")))
    busy_intervals.append((time_to_minutes("15:00"), time_to_minutes("17:00")))
    
    # Kyle
    busy_intervals.append((time_to_minutes("9:00"), time_to_minutes("9:30")))
    busy_intervals.append((time_to_minutes("11:30"), time_to_minutes("12:00")))
    busy_intervals.append((time_to_minutes("12:30"), time_to_minutes("13:00")))
    busy_intervals.append((time_to_minutes("14:30"), time_to_minutes("17:00")))
    
    # Merge busy intervals
    if not busy_intervals:
        merged = []
    else:
        busy_intervals.sort(key=lambda x: x[0])
        merged = []
        current_start, current_end = busy_intervals[0]
        for interval in busy_intervals[1:]:
            s, e = interval
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))
    
    # Find free intervals
    free_intervals = []
    current = work_start
    
    for start, end in merged:
        if start > current:
            gap = start - current
            if gap >= meeting_duration:
                free_intervals.append((current, start))
        current = end
    
    if work_end - current >= meeting_duration:
        free_intervals.append((current, work_end))
    
    # Choose the earliest free interval
    if free_intervals:
        meeting_start_minutes = free_intervals[0][0]
        meeting_end_minutes = meeting_start_minutes + meeting_duration
        start_time = minutes_to_time(meeting_start_minutes)
        end_time = minutes_to_time(meeting_end_minutes)
        print(f"Monday {start_time}:{end_time}")
    else:
        # According to the problem, there is a solution, so this should not happen
        print("No suitable time found")

if __name__ == "__main__":
    main()