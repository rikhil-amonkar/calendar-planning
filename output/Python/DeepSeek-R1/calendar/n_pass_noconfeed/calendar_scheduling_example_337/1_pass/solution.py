def time_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    work_start = time_to_minutes("9:00")  # 540
    work_end = time_to_minutes("17:00")   # 1020
    
    john_meetings = ["11:30 to 12:00", "14:00 to 14:30"]
    megan_meetings = ["12:00 to 12:30", "14:00 to 15:00", "15:30 to 16:00"]
    brandon_meetings = []
    kimberly_meetings = ["9:00 to 9:30", "10:00 to 10:30", "11:00 to 14:30", "15:00 to 16:00", "16:30 to 17:00"]
    sean_meetings = ["10:00 to 11:00", "11:30 to 14:00", "15:00 to 15:30"]
    lori_meetings = ["9:00 to 9:30", "10:30 to 12:00", "13:00 to 14:30", "16:00 to 16:30"]
    
    all_busy = []
    
    for m in john_meetings:
        parts = m.split(' to ')
        s_min = time_to_minutes(parts[0])
        e_min = time_to_minutes(parts[1])
        all_busy.append((s_min, e_min))
        
    for m in megan_meetings:
        parts = m.split(' to ')
        s_min = time_to_minutes(parts[0])
        e_min = time_to_minutes(parts[1])
        all_busy.append((s_min, e_min))
        
    for m in kimberly_meetings:
        parts = m.split(' to ')
        s_min = time_to_minutes(parts[0])
        e_min = time_to_minutes(parts[1])
        all_busy.append((s_min, e_min))
        
    for m in sean_meetings:
        parts = m.split(' to ')
        s_min = time_to_minutes(parts[0])
        e_min = time_to_minutes(parts[1])
        all_busy.append((s_min, e_min))
        
    for m in lori_meetings:
        parts = m.split(' to ')
        s_min = time_to_minutes(parts[0])
        e_min = time_to_minutes(parts[1])
        all_busy.append((s_min, e_min))
        
    if not all_busy:
        merged_busy = []
    else:
        sorted_busy = sorted(all_busy, key=lambda x: x[0])
        merged_busy = []
        current_start, current_end = sorted_busy[0]
        for interval in sorted_busy[1:]:
            if interval[0] <= current_end:
                if interval[1] > current_end:
                    current_end = interval[1]
            else:
                merged_busy.append((current_start, current_end))
                current_start, current_end = interval
        merged_busy.append((current_start, current_end))
    
    free_intervals = []
    if not merged_busy:
        free_intervals.append((work_start, work_end))
    else:
        if merged_busy[0][0] > work_start:
            free_intervals.append((work_start, merged_busy[0][0]))
        for i in range(len(merged_busy) - 1):
            free_start = merged_busy[i][1]
            free_end = merged_busy[i+1][0]
            if free_start < free_end:
                free_intervals.append((free_start, free_end))
        if merged_busy[-1][1] < work_end:
            free_intervals.append((merged_busy[-1][1], work_end))
    
    meeting_start = None
    meeting_end = None
    for start, end in free_intervals:
        if end - start >= 30:
            meeting_start = start
            meeting_end = start + 30
            break
    
    if meeting_start is None:
        print("No suitable time found.")
    else:
        start_str = minutes_to_time(meeting_start)
        end_str = minutes_to_time(meeting_end)
        time_range_str = f"{start_str}:{end_str}"
        print("Monday")
        print(time_range_str)

if __name__ == "__main__":
    main()