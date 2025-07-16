def intersect_intervals(intervals_a, intervals_b):
    i, j = 0, 0
    result = []
    while i < len(intervals_a) and j < len(intervals_b):
        a_start, a_end = intervals_a[i]
        b_start, b_end = intervals_b[j]
        low = max(a_start, b_start)
        high = min(a_end, b_end)
        if low < high:
            result.append((low, high))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result

def main():
    work_start_min = 0
    work_end_min = 480  # 9:00 to 17:00 is 8 hours = 480 minutes
    
    blocked_times = {
        'Diane': [(30, 60), (330, 360)],
        'Jack': [(270, 300), (330, 360)],
        'Eugene': [(0, 60), (90, 150), (180, 330), (360, 450)],
        'Patricia': [(30, 90), (120, 180), (210, 300), (360, 450)]
    }
    
    free_intervals = {}
    for name, blocks in blocked_times.items():
        sorted_blocks = sorted(blocks, key=lambda x: x[0])
        free = []
        current = work_start_min
        for (s, e) in sorted_blocks:
            if current < s:
                free.append((current, s))
            current = e
        if current < work_end_min:
            free.append((current, work_end_min))
        free_intervals[name] = free
    
    common = free_intervals['Diane']
    for name in ['Jack', 'Eugene', 'Patricia']:
        common = intersect_intervals(common, free_intervals[name])
    
    meeting_start = None
    for (s, e) in common:
        if e - s >= 30:
            meeting_start = s
            break
    
    if meeting_start is None:
        print("No solution found")
        return
    
    meeting_end = meeting_start + 30
    s_hour = 9 + meeting_start // 60
    s_minute = meeting_start % 60
    e_hour = 9 + meeting_end // 60
    e_minute = meeting_end % 60
    
    s_hour_str = str(int(s_hour)).zfill(2)
    s_minute_str = str(int(s_minute)).zfill(2)
    e_hour_str = str(int(e_hour)).zfill(2)
    e_minute_str = str(int(e_minute)).zfill(2)
    
    time_range_str = f"{s_hour_str}:{s_minute_str}:{e_hour_str}:{e_minute_str}"
    print("Monday")
    print(time_range_str)

if __name__ == "__main__":
    main()