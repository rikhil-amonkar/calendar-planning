def main():
    # Convert work hours to minutes
    work_start = 9 * 60  # 9:00
    work_end = 17 * 60   # 17:00

    # Tuesday's busy intervals for Betty (in minutes)
    betty_busy = [
        (9*60+30, 10*60),   # 9:30-10:00
        (10*60+30, 11*60),  # 10:30-11:00
        (12*60, 12*60+30),  # 12:00-12:30
        (13*60+30, 15*60),  # 13:30-15:00
        (16*60+30, 17*60)   # 16:30-17:00
    ]

    # Tuesday's busy intervals for Megan
    megan_busy = [
        (9*60, 9*60+30),    # 9:00-9:30
        (10*60, 10*60+30),  # 10:00-10:30
        (12*60, 14*60),     # 12:00-14:00
        (15*60, 15*60+30),  # 15:00-15:30
        (16*60, 16*60+30)   # 16:00-16:30
    ]

    # Combine and sort all busy intervals
    combined_busy = sorted(betty_busy + megan_busy)
    merged_busy = []
    
    if combined_busy:
        start_curr, end_curr = combined_busy[0]
        for i in range(1, len(combined_busy)):
            s, e = combined_busy[i]
            if s <= end_curr:
                end_curr = max(end_curr, e)
            else:
                merged_busy.append((start_curr, end_curr))
                start_curr, end_curr = s, e
        merged_busy.append((start_curr, end_curr))

    # Calculate free intervals
    free_intervals = []
    current = work_start
    for start, end in merged_busy:
        if current < start:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))

    # Find first available 60-minute slot
    for start, end in free_intervals:
        if end - start >= 60:
            meeting_start = start
            meeting_end = start + 60
            # Convert to time string
            start_hr = meeting_start // 60
            start_min = meeting_start % 60
            end_hr = meeting_end // 60
            end_min = meeting_end % 60
            time_str = f"{start_hr:02d}:{start_min:02d}:{end_hr:02d}:{end_min:02d}"
            print("Tuesday")
            print(time_str)
            return
    
    print("No suitable time found")

if __name__ == "__main__":
    main()