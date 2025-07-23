def invert_busy(busy_list, start, end):
    if not busy_list:
        return [(start, end)]
    sorted_busy = sorted(busy_list, key=lambda x: x[0])
    free = []
    current = start
    for interval in sorted_busy:
        s_busy, e_busy = interval
        if current < s_busy:
            free.append((current, s_busy))
        current = max(current, e_busy)
    if current < end:
        free.append((current, end))
    return free

def intersect_intervals(intervals1, intervals2):
    i = 0
    j = 0
    res = []
    while i < len(intervals1) and j < len(intervals2):
        s1, e1 = intervals1[i]
        s2, e2 = intervals2[j]
        low = max(s1, s2)
        high = min(e1, e2)
        if low < high:
            res.append((low, high))
        if e1 < e2:
            i += 1
        else:
            j += 1
    return res

def main():
    work_start = 540  # 9:00 in minutes
    work_end = 1020   # 17:00 in minutes
    constraint_time = 720  # 12:00 in minutes for Monday constraint

    busy_times = {
        'Monday': {
            'Joshua': [(15*60, 15*60+30)],
            'Joyce': [
                (9*60, 9*60+30),
                (10*60, 11*60),
                (11*60+30, 12*60+30),
                (13*60, 15*60),
                (15*60+30, 17*60)
            ]
        },
        'Tuesday': {
            'Joshua': [
                (11*60+30, 12*60),
                (13*60, 13*60+30),
                (14*60+30, 15*60)
            ],
            'Joyce': [
                (9*60, 17*60)
            ]
        },
        'Wednesday': {
            'Joshua': [],
            'Joyce': [
                (9*60, 9*60+30),
                (10*60, 11*60),
                (12*60+30, 15*60+30),
                (16*60, 16*60+30)
            ]
        }
    }
    
    days_to_check = ['Monday', 'Wednesday']  # Skip Tuesday since Joyce is busy all day
    found = False
    result_day = None
    result_time_str = None
    
    for day in days_to_check:
        busy_joshua = busy_times[day]['Joshua']
        busy_joyce = busy_times[day]['Joyce']
        
        free_joshua = invert_busy(busy_joshua, work_start, work_end)
        free_joyce = invert_busy(busy_joyce, work_start, work_end)
        
        if day == 'Monday':
            adjusted_free_joyce = []
            for interval in free_joyce:
                s, e = interval
                if e <= constraint_time:
                    continue
                if s < constraint_time:
                    s = constraint_time
                if e - s >= 30:
                    adjusted_free_joyce.append((s, e))
            free_joyce = adjusted_free_joyce
        
        common_free = intersect_intervals(free_joshua, free_joyce)
        
        for interval in common_free:
            s, e = interval
            if e - s >= 30:
                meeting_start = s
                meeting_end = s + 30
                start_hour = meeting_start // 60
                start_minute = meeting_start % 60
                end_hour = meeting_end // 60
                end_minute = meeting_end % 60
                time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
                result_day = day
                result_time_str = time_str
                found = True
                break
        if found:
            break
    
    if found:
        print(result_day)
        print(result_time_str)
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()