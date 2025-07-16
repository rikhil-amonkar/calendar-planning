def main():
    work_start_min = 9 * 60  # 9:00 in minutes
    work_end_min = 17 * 60   # 17:00 in minutes
    helen_constraint_end = 13 * 60 + 30  # 13:30 in minutes
    meeting_duration = 30

    margaret_busy = [
        [9*60, 10*60],     # 9:00-10:00
        [10*60+30, 11*60], # 10:30-11:00
        [11*60+30, 12*60], # 11:30-12:00
        [13*60, 13*60+30], # 13:00-13:30
        [15*60, 15*60+30]  # 15:00-15:30
    ]
    
    donna_busy = [
        [14*60+30, 15*60], # 14:30-15:00
        [16*60, 16*60+30]  # 16:00-16:30
    ]
    
    helen_busy = [
        [9*60, 9*60+30],   # 9:00-9:30
        [10*60, 11*60+30], # 10:00-11:30
        [13*60, 14*60],    # 13:00-14:00
        [14*60+30, 15*60], # 14:30-15:00
        [15*60+30, 17*60]  # 15:30-17:00
    ]
    
    all_busy = []
    
    for interval in margaret_busy:
        s, e = interval
        if e <= work_start_min or s >= helen_constraint_end:
            continue
        s_clip = max(s, work_start_min)
        e_clip = min(e, helen_constraint_end)
        if s_clip < e_clip:
            all_busy.append([s_clip, e_clip])
    
    for interval in donna_busy:
        s, e = interval
        if e <= work_start_min or s >= helen_constraint_end:
            continue
        s_clip = max(s, work_start_min)
        e_clip = min(e, helen_constraint_end)
        if s_clip < e_clip:
            all_busy.append([s_clip, e_clip])
    
    for interval in helen_busy:
        s, e = interval
        if e <= work_start_min or s >= helen_constraint_end:
            continue
        s_clip = max(s, work_start_min)
        e_clip = min(e, helen_constraint_end)
        if s_clip < e_clip:
            all_busy.append([s_clip, e_clip])
    
    if not all_busy:
        merged_busy = []
    else:
        all_busy.sort(key=lambda x: x[0])
        merged_busy = []
        start_curr, end_curr = all_busy[0]
        for i in range(1, len(all_busy)):
            s, e = all_busy[i]
            if s <= end_curr:
                if e > end_curr:
                    end_curr = e
            else:
                merged_busy.append([start_curr, end_curr])
                start_curr, end_curr = s, e
        merged_busy.append([start_curr, end_curr])
    
    free_intervals = []
    current = work_start_min
    for interval in merged_busy:
        s, e = interval
        if current < s:
            free_intervals.append([current, s])
            current = e
        else:
            if e > current:
                current = e
    if current < helen_constraint_end:
        free_intervals.append([current, helen_constraint_end])
    
    meeting_start = None
    for interval in free_intervals:
        start_free, end_free = interval
        if end_free - start_free >= meeting_duration:
            meeting_start = start_free
            break
    
    if meeting_start is None:
        print("No suitable time found")
        return
    
    meeting_end = meeting_start + meeting_duration
    
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    
    print("Monday")
    print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()