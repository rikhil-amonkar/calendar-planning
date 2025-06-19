def time_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

def main():
    day = input().strip()
    work_start_str, work_end_str = input().split()
    work_start = time_to_minutes(work_start_str)
    work_end = time_to_minutes(work_end_str)
    
    n = int(input().strip())
    busy_minutes = []
    for i in range(n):
        s, e = input().split()
        s_min = time_to_minutes(s)
        e_min = time_to_minutes(e)
        s_min = max(s_min, work_start)
        e_min = min(e_min, work_end)
        if s_min < e_min:
            busy_minutes.append((s_min, e_min))
    
    busy_minutes.sort(key=lambda x: x[0])
    
    free_intervals = []
    current = work_start
    for s, e in busy_minutes:
        if s > current:
            gap_duration = s - current
            if gap_duration >= 30:
                free_intervals.append((current, s))
        current = max(current, e)
    if work_end - current >= 30:
        free_intervals.append((current, work_end))
    
    meeting_slot = None
    for interval in free_intervals:
        s, e = interval
        aligned_start = ((s + 14) // 15) * 15
        if aligned_start + 30 <= e:
            meeting_slot = (aligned_start, aligned_start + 30)
            break
    
    if meeting_slot:
        start_time = minutes_to_time(meeting_slot[0])
        end_time = minutes_to_time(meeting_slot[1])
        print(day)
        print(f"{start_time}-{end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()