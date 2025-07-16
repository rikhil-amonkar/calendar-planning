def time_str_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def compute_free_intervals(busy_intervals, work_start_min, work_end_min):
    if not busy_intervals:
        return [[work_start_min, work_end_min]]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current = work_start_min
    for start, end in sorted_busy:
        if current < start:
            free.append([current, start])
        current = max(current, end)
    if current < work_end_min:
        free.append([current, work_end_min])
    return free

def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        s1, e1 = intervals1[i]
        s2, e2 = intervals2[j]
        start_max = max(s1, s2)
        end_min = min(e1, e2)
        if start_max < end_min:
            intersections.append([start_max, end_min])
        if e1 < e2:
            i += 1
        else:
            j += 1
    return intersections

def main():
    work_start = "09:00"
    work_end = "17:00"
    meeting_duration = 30
    day = "Monday"
    
    denise_busy = [["12:00", "12:30"], ["15:30", "16:00"]]
    angela_busy = []
    natalie_busy = [["09:00", "11:30"], ["12:00", "13:00"], ["14:00", "14:30"], ["15:00", "17:00"]]
    
    work_start_min = time_str_to_minutes(work_start)
    work_end_min = time_str_to_minutes(work_end)
    
    denise_busy_min = [[time_str_to_minutes(s), time_str_to_minutes(e)] for s, e in denise_busy]
    angela_busy_min = [[time_str_to_minutes(s), time_str_to_minutes(e)] for s, e in angela_busy]
    natalie_busy_min = [[time_str_to_minutes(s), time_str_to_minutes(e)] for s, e in natalie_busy]
    
    denise_free = compute_free_intervals(denise_busy_min, work_start_min, work_end_min)
    angela_free = compute_free_intervals(angela_busy_min, work_start_min, work_end_min)
    natalie_free = compute_free_intervals(natalie_busy_min, work_start_min, work_end_min)
    
    common_free = intersect_intervals(denise_free, angela_free)
    common_free = intersect_intervals(common_free, natalie_free)
    
    meeting_start = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_start = start
            break
    
    meeting_end = meeting_start + meeting_duration
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    time_range = f"{start_str}:{end_str}"
    
    print(time_range)
    print(day)

if __name__ == "__main__":
    main()