def get_free_intervals(busy_list, min_t, max_t):
    events = []
    for (s, e) in busy_list:
        if e <= min_t or s >= max_t:
            continue
        s_clamped = max(s, min_t)
        e_clamped = min(e, max_t)
        events.append((s_clamped, e_clamped))
    
    if not events:
        return [(min_t, max_t)]
    
    events.sort(key=lambda x: x[0])
    merged = []
    start_curr, end_curr = events[0]
    for i in range(1, len(events)):
        s, e = events[i]
        if s <= end_curr:
            end_curr = max(end_curr, e)
        else:
            merged.append((start_curr, end_curr))
            start_curr, end_curr = s, e
    merged.append((start_curr, end_curr))
    
    free_intervals = []
    current = min_t
    for (s, e) in merged:
        if s > current:
            free_intervals.append((current, s))
        current = e
    if current < max_t:
        free_intervals.append((current, max_t))
    
    return free_intervals

def main():
    work_start = 9 * 60
    work_end = 17 * 60
    meeting_duration = 30
    
    betty_busy = {
        "Tuesday": [
            (9*60, 9*60+30),
            (11*60+30, 12*60),
            (12*60+30, 13*60),
            (13*60+30, 14*60),
            (16*60+30, 17*60)
        ],
        "Wednesday": [
            (9*60+30, 10*60+30),
            (13*60, 13*60+30),
            (14*60, 14*60+30)
        ],
        "Thursday": [
            (9*60+30, 10*60),
            (11*60+30, 12*60),
            (14*60, 14*60+30),
            (15*60, 15*60+30),
            (16*60+30, 17*60)
        ]
    }
    
    scott_busy = {
        "Tuesday": [
            (9*60, 9*60+30),
            (10*60, 11*60),
            (11*60+30, 12*60),
            (12*60+30, 13*60+30),
            (14*60, 15*60),
            (16*60, 16*60+30)
        ],
        "Wednesday": [
            (9*60+30, 12*60+30),
            (13*60, 13*60+30),
            (14*60, 14*60+30),
            (15*60, 15*60+30),
            (16*60, 16*60+30)
        ],
        "Thursday": [
            (9*60, 9*60+30),
            (10*60, 10*60+30),
            (11*60, 12*60),
            (12*60+30, 13*60),
            (15*60, 16*60),
            (16*60+30, 17*60)
        ]
    }
    
    days_order = ['Tuesday', 'Wednesday', 'Thursday']
    
    for day in days_order:
        if day in ['Tuesday', 'Thursday']:
            min_betty = 15 * 60
        else:
            min_betty = work_start
        
        betty_free = get_free_intervals(betty_busy.get(day, []), min_betty, work_end)
        scott_free = get_free_intervals(scott_busy.get(day, []), work_start, work_end)
        
        for b_int in betty_free:
            for s_int in scott_free:
                overlap_start = max(b_int[0], s_int[0])
                overlap_end = min(b_int[1], s_int[1])
                if overlap_end - overlap_start >= meeting_duration:
                    slot_start = overlap_start
                    slot_end = slot_start + meeting_duration
                    
                    start_h = slot_start // 60
                    start_m = slot_start % 60
                    end_h = slot_end // 60
                    end_m = slot_end % 60
                    
                    time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
                    print(time_str)
                    print(day)
                    return
                    
    print("No suitable time found")

if __name__ == "__main__":
    main()