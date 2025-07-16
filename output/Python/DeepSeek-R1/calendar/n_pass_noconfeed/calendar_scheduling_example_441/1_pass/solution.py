def main():
    work_start = 540  # 9:00 in minutes
    work_end = 1020   # 17:00
    duration = 30

    # List of busy intervals (start, end) in minutes
    busy = [
        # Joan
        (11*60+30, 12*60),    # 11:30-12:00
        (14*60+30, 15*60),    # 14:30-15:00

        # Megan
        (9*60, 10*60),        # 9:00-10:00
        (14*60, 14*60+30),    # 14:00-14:30
        (16*60, 16*60+30),    # 16:00-16:30

        # Austin: none

        # Betty
        (9*60+30, 10*60),     # 9:30-10:00
        (11*60+30, 12*60),    # 11:30-12:00
        (13*60+30, 14*60),    # 13:30-14:00
        (16*60, 16*60+30),    # 16:00-16:30

        # Judith
        (9*60, 11*60),        # 9:00-11:00
        (12*60, 13*60),       # 12:00-13:00
        (14*60, 15*60),       # 14:00-15:00

        # Terry
        (9*60+30, 10*60),     # 9:30-10:00
        (11*60+30, 12*60+30), # 11:30-12:30
        (13*60, 14*60),       # 13:00-14:00
        (15*60, 15*60+30),    # 15:00-15:30
        (16*60, 17*60),       # 16:00-17:00

        # Kathryn
        (9*60+30, 10*60),     # 9:30-10:00
        (10*60+30, 11*60),    # 10:30-11:00
        (11*60+30, 13*60),    # 11:30-13:00
        (14*60, 16*60),       # 14:00-16:00
        (16*60+30, 17*60)     # 16:30-17:00
    ]

    # Sort by start time
    busy_sorted = sorted(busy, key=lambda x: x[0])
    
    # Merge intervals
    merged = []
    for interval in busy_sorted:
        if not merged:
            merged.append(interval)
        else:
            last_start, last_end = merged[-1]
            current_start, current_end = interval
            if current_start <= last_end:
                merged[-1] = (last_start, max(last_end, current_end))
            else:
                merged.append(interval)

    # Find free intervals within work hours
    free_intervals = []
    # Before first busy interval
    if merged[0][0] > work_start:
        free_intervals.append((work_start, merged[0][0]))
    
    # Between busy intervals
    for i in range(1, len(merged)):
        prev_end = merged[i-1][1]
        next_start = merged[i][0]
        if prev_end < next_start:
            free_intervals.append((prev_end, next_start))
    
    # After last busy interval
    if merged[-1][1] < work_end:
        free_intervals.append((merged[-1][1], work_end))
    
    # Find first free slot of at least 30 minutes
    for start, end in free_intervals:
        if end - start >= duration:
            meeting_start = start
            meeting_end = meeting_start + duration
            break
    
    # Convert to HH:MM format
    start_hour = meeting_start // 60
    start_min = meeting_start % 60
    end_hour = meeting_end // 60
    end_min = meeting_end % 60
    
    time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
    print("Monday", time_str)

if __name__ == "__main__":
    main()