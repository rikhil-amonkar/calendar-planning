def main():
    work_start_abs = 9 * 60
    work_end_abs = 17 * 60

    def parse_time(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return hour * 60 + minute

    busy_intervals = []
    
    # Emily's meetings
    busy_intervals.append([parse_time("10:00"), parse_time("10:30")])
    busy_intervals.append([parse_time("16:00"), parse_time("16:30")])
    
    # Maria's meetings
    busy_intervals.append([parse_time("10:30"), parse_time("11:00")])
    
    # Carl's meetings
    busy_intervals.append([parse_time("9:30"), parse_time("10:00")])
    busy_intervals.append([parse_time("10:30"), parse_time("12:30")])
    busy_intervals.append([parse_time("13:30"), parse_time("14:00")])
    busy_intervals.append([parse_time("14:30"), parse_time("15:30")])
    busy_intervals.append([parse_time("16:00"), parse_time("17:00")])
    
    # David's meetings
    busy_intervals.append([parse_time("9:30"), parse_time("11:00")])
    busy_intervals.append([parse_time("11:30"), parse_time("12:00")])
    busy_intervals.append([parse_time("12:30"), parse_time("13:30")])
    busy_intervals.append([parse_time("14:00"), parse_time("15:00")])
    busy_intervals.append([parse_time("16:00"), parse_time("17:00")])
    
    # Frank's meetings
    busy_intervals.append([parse_time("9:30"), parse_time("10:30")])
    busy_intervals.append([parse_time("11:00"), parse_time("11:30")])
    busy_intervals.append([parse_time("12:30"), parse_time("13:30")])
    busy_intervals.append([parse_time("14:30"), parse_time("17:00")])
    
    if not busy_intervals:
        merged = []
    else:
        sorted_intervals = sorted(busy_intervals, key=lambda x: x[0])
        merged = [sorted_intervals[0]]
        for i in range(1, len(sorted_intervals)):
            current_interval = sorted_intervals[i]
            last_merged = merged[-1]
            if current_interval[0] <= last_merged[1]:
                merged[-1][1] = max(last_merged[1], current_interval[1])
            else:
                merged.append(current_interval)
                
    free_intervals = []
    current = work_start_abs
    for interval in merged:
        s, e = interval
        if current < s:
            free_intervals.append([current, s])
            current = e
        else:
            if e > current:
                current = e
    if current < work_end_abs:
        free_intervals.append([current, work_end_abs])
        
    meeting_start_abs = None
    for interval in free_intervals:
        start_free, end_free = interval
        if end_free - start_free >= 30:
            meeting_start_abs = start_free
            break
            
    if meeting_start_abs is None:
        meeting_start_abs = work_start_abs
        
    meeting_end_abs = meeting_start_abs + 30
    
    start_h = meeting_start_abs // 60
    start_m = meeting_start_abs % 60
    end_h = meeting_end_abs // 60
    end_m = meeting_end_abs % 60
    
    print(f"Monday {start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}")

if __name__ == "__main__":
    main()