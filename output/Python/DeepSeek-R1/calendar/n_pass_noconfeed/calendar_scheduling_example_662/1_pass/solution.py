def subtract_interval(intervals, to_remove):
    new_intervals = []
    r_start, r_end = to_remove
    for start, end in intervals:
        if end <= r_start or start >= r_end:
            new_intervals.append((start, end))
        else:
            if r_start <= start and r_end >= end:
                continue
            elif r_start > start and r_end < end:
                new_intervals.append((start, r_start))
                new_intervals.append((r_end, end))
            elif r_start <= start and r_end < end:
                new_intervals.append((r_end, end))
            elif r_start > start and r_end >= end:
                new_intervals.append((start, r_start))
    return new_intervals

def merge_avail(intervals1, intervals2):
    intervals1_sorted = sorted(intervals1, key=lambda x: x[0])
    intervals2_sorted = sorted(intervals2, key=lambda x: x[0])
    i = j = 0
    common = []
    while i < len(intervals1_sorted) and j < len(intervals2_sorted):
        a1, a2 = intervals1_sorted[i]
        b1, b2 = intervals2_sorted[j]
        low = max(a1, b1)
        high = min(a2, b2)
        if low < high:
            common.append((low, high))
        if a2 < b2:
            i += 1
        else:
            j += 1
    return common

def main():
    work_start = 540  # 9:00 in minutes
    work_end = 1020    # 17:00 in minutes
    days = ['Monday', 'Tuesday']
    
    gary_busy = {
        'Monday': [(570, 600), (660, 780), (840, 870), (990, 1020)],
        'Tuesday': [(540, 570), (630, 660), (870, 960)]
    }
    
    david_busy = {
        'Monday': [(540, 570), (600, 780), (870, 990)],
        'Tuesday': [(540, 570), (600, 630), (660, 750), (780, 870), (900, 960), (990, 1020)]
    }
    
    meeting_duration = 60  # minutes
    result_day = None
    result_time = None
    
    for day in days:
        gary_avail = [(work_start, work_end)]
        for busy in gary_busy[day]:
            gary_avail = subtract_interval(gary_avail, busy)
        
        david_avail = [(work_start, work_end)]
        for busy in david_busy[day]:
            david_avail = subtract_interval(david_avail, busy)
        
        common_avail = merge_avail(gary_avail, david_avail)
        for start, end in common_avail:
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = meeting_start + meeting_duration
                start_hour = meeting_start // 60
                start_minute = meeting_start % 60
                end_hour = meeting_end // 60
                end_minute = meeting_end % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                result_time = f"{start_str}:{end_str}"
                result_day = day
                break
        if result_day:
            break
    
    if result_day:
        print(result_day)
        print(result_time)
    else:
        print("No suitable time found")

if __name__ == '__main__':
    main()