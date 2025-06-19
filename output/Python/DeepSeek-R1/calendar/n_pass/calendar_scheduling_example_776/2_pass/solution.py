def time_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

def main():
    day = "Monday"
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("14:30")
    
    busy_intervals = [
        ("09:00", "11:00"),
        ("11:30", "13:00"),
        ("13:30", "14:30"),
        ("15:00", "17:00")
    ]
    busy_minutes = []
    for s, e in busy_intervals:
        s_min = time_to_minutes(s)
        e_min = time_to_minutes(e)
        if s_min < work_end:
            e_min = min(e_min, work_end)
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
    for s, e in free_intervals:
        aligned_start = ((s + 14) // 15) * 15
        if aligned_start + 30 <= e:
            meeting_slot = (aligned_start, aligned_start + 30)
            break
    
    if meeting_slot:
        start_time = minutes_to_time(meeting_slot[0])
        end_time = minutes_to_time(meeting_slot[1])
        print(day)
        print(f"{start_time}:{end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()