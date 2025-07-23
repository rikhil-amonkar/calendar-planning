def free_intervals(busy_list, work_start, work_end):
    if not busy_list:
        return [[work_start, work_end]]
    busy_list.sort(key=lambda x: x[0])
    free = []
    current = work_start
    for start_busy, end_busy in busy_list:
        if current < start_busy:
            free.append([current, start_busy])
        current = max(current, end_busy)
    if current < work_end:
        free.append([current, work_end])
    return free

def intersect_intervals(intervalsA, intervalsB):
    i, j = 0, 0
    result = []
    while i < len(intervalsA) and j < len(intervalsB):
        a_start, a_end = intervalsA[i]
        b_start, b_end = intervalsB[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            result.append([start, end])
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result

def main():
    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    work_start = 540
    work_end = 1020
    duration = 30
    
    # Juan cannot meet after 16:00 (960 minutes)
    busy_juan = [[540, 630], [930, 960]]  # 9:00-10:30, 15:30-16:00
    free_juan = free_intervals(busy_juan, work_start, 960)  # work_end for Juan is 16:00
    
    busy_marilyn = [[660, 690], [750, 780]]  # 11:00-11:30, 12:30-13:00
    free_marilyn = free_intervals(busy_marilyn, work_start, work_end)
    
    busy_ronald = [[540, 630], [720, 750], [780, 810], [840, 990]]  # 9:00-10:30, 12:00-12:30, 13:00-13:30, 14:00-16:30
    free_ronald = free_intervals(busy_ronald, work_start, work_end)
    
    # Find common free intervals
    common = intersect_intervals(free_juan, free_marilyn)
    common = intersect_intervals(common, free_ronald)
    
    # Find the first slot of at least 30 minutes
    meeting_start = None
    for start, end in common:
        if end - start >= duration:
            meeting_start = start
            break
    
    # Convert meeting_start to time
    start_h = meeting_start // 60
    start_m = meeting_start % 60
    meeting_end = meeting_start + duration
    end_h = meeting_end // 60
    end_m = meeting_end % 60
    
    # Format the time string
    time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
    
    # Output
    print("Monday")
    print(time_str)

if __name__ == "__main__":
    main()