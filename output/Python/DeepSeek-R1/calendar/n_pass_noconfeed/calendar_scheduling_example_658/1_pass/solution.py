def main():
    # Define work hours (9:00 to 17:00) in minutes
    work_start = 9 * 60   # 540 minutes (9:00)
    work_end = 17 * 60    # 1020 minutes (17:00)
    meeting_duration = 30  # 30 minutes

    # Busy intervals for each participant per day in minutes
    busy_times = {
        'Monday': {
            'Shirley': [(630, 660), (720, 750), (960, 990)],
            'Albert': [(540, 1020)]
        },
        'Tuesday': {
            'Shirley': [(570, 600)],
            'Albert': [(570, 660), (690, 750), (780, 960), (990, 1020)]
        }
    }
    
    days = ['Monday', 'Tuesday']
    tuesday_cutoff = 10 * 60 + 30  # 10:30 in minutes (630)
    found = False
    result_day = None
    result_start = None

    for day in days:
        # Combine all busy intervals for the day
        all_busy = []
        for intervals in busy_times[day].values():
            all_busy.extend(intervals)
        
        # Sort busy intervals by start time
        all_busy.sort(key=lambda x: x[0])
        
        # Merge overlapping intervals
        merged = []
        for start, end in all_busy:
            if not merged:
                merged.append((start, end))
            else:
                last_start, last_end = merged[-1]
                if start <= last_end:
                    merged[-1] = (last_start, max(last_end, end))
                else:
                    merged.append((start, end))
        
        # Calculate free intervals within work hours
        free_intervals = []
        current = work_start
        for start, end in merged:
            if current < start:
                free_intervals.append((current, start))
            current = end
        if current < work_end:
            free_intervals.append((current, work_end))
        
        # Check for a suitable meeting slot
        if day == 'Tuesday':
            # First pass: try to find a slot ending by 10:30 (preference)
            for start_free, end_free in free_intervals:
                if end_free - start_free >= meeting_duration:
                    if start_free + meeting_duration <= tuesday_cutoff:
                        result_day = day
                        result_start = start_free
                        found = True
                        break
            if found:
                break
            # Second pass: any available slot on Tuesday
            for start_free, end_free in free_intervals:
                if end_free - start_free >= meeting_duration:
                    result_day = day
                    result_start = start_free
                    found = True
                    break
            if found:
                break
        else:  # Monday
            for start_free, end_free in free_intervals:
                if end_free - start_free >= meeting_duration:
                    result_day = day
                    result_start = start_free
                    found = True
                    break
            if found:
                break
    
    # Format the result
    def format_minutes(m):
        h = m // 60
        m = m % 60
        return f"{h:02d}:{m:02d}"
    
    start_time = format_minutes(result_start)
    end_time = format_minutes(result_start + meeting_duration)
    time_range_str = f"{start_time}:{end_time}"
    print(f"{result_day} {time_range_str}")

if __name__ == "__main__":
    main()