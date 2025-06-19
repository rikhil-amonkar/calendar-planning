def main():
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    busy_intervals = [
        # Stephen
        (10 * 60, 10 * 60 + 30),  # 10:00-10:30
        (12 * 60, 12 * 60 + 30),  # 12:00-12:30
        # Brittany
        (11 * 60, 11 * 60 + 30),  # 11:00-11:30
        (13 * 60 + 30, 14 * 60),  # 13:30-14:00
        (15 * 60 + 30, 16 * 60),  # 15:30-16:00
        (16 * 60 + 30, 17 * 60),  # 16:30-17:00
        # Dorothy
        (9 * 60, 9 * 60 + 30),    # 9:00-9:30
        (10 * 60, 10 * 60 + 30),  # 10:00-10:30
        (11 * 60, 12 * 60 + 30),  # 11:00-12:30
        (13 * 60, 15 * 60),       # 13:00-15:00
        (15 * 60 + 30, 17 * 60),  # 15:30-17:00
        # Rebecca
        (9 * 60 + 30, 10 * 60 + 30),  # 9:30-10:30
        (11 * 60, 11 * 60 + 30),      # 11:00-11:30
        (12 * 60, 12 * 60 + 30),      # 12:00-12:30
        (13 * 60, 17 * 60),           # 13:00-17:00
        # Jordan
        (9 * 60, 9 * 60 + 30),        # 9:00-9:30
        (10 * 60, 11 * 60),           # 10:00-11:00
        (11 * 60 + 30, 12 * 60),      # 11:30-12:00
        (13 * 60, 15 * 60),           # 13:00-15:00
        (15 * 60 + 30, 16 * 60 + 30)  # 15:30-16:30
    ]
    
    if not busy_intervals:
        free_intervals = [(work_start, work_end)]
    else:
        sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
        merged = []
        start_curr, end_curr = sorted_busy[0]
        for i in range(1, len(sorted_busy)):
            s, e = sorted_busy[i]
            if s <= end_curr:
                end_curr = max(end_curr, e)
            else:
                merged.append((start_curr, end_curr))
                start_curr, end_curr = s, e
        merged.append((start_curr, end_curr))
        
        free_intervals = []
        current = work_start
        for s, e in merged:
            if current < s:
                free_intervals.append((current, s))
            current = max(current, e)
        if current < work_end:
            free_intervals.append((current, work_end))
    
    meeting_start = None
    meeting_end = None
    for s, e in free_intervals:
        if e - s >= 30:
            meeting_start = s
            meeting_end = s + 30
            break
    
    if meeting_start is None:
        print("No suitable time found")
        return
    
    start_hour = meeting_start // 60
    start_min = meeting_start % 60
    end_hour = meeting_end // 60
    end_min = meeting_end % 60
    
    start_str = f"{start_hour:02d}:{start_min:02d}"
    end_str = f"{end_hour:02d}:{end_min:02d}"
    
    print("Monday")
    print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()