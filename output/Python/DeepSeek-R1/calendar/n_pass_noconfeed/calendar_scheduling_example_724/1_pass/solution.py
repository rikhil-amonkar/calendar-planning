def main():
    # Work hours: 9:00 to 17:00 (in minutes: 540 to 1020)
    work_start = 540
    work_end = 1020
    days = ['Monday', 'Tuesday', 'Wednesday']
    meeting_duration = 30  # minutes

    # Tyler's busy times in minutes (start, end)
    tyler_busy = {
        'Tuesday': [(540, 570), (870, 900)],  # 9:00-9:30, 14:30-15:00
        'Wednesday': [(630, 660), (750, 780), (810, 840), (990, 1020)],  # 10:30-11:00, 12:30-13:00, 13:30-14:00, 16:30-17:00
        'Monday': []  # No busy times on Monday
    }

    # Ruth's busy times in minutes (start, end)
    ruth_busy = {
        'Monday': [(540, 600), (630, 720), (750, 870), (900, 960), (990, 1020)],  # 9:00-10:00, 10:30-12:00, 12:30-14:30, 15:00-16:00, 16:30-17:00
        'Tuesday': [(540, 1020)],  # Entire work day
        'Wednesday': [(540, 1020)]  # Entire work day
    }

    # Additional constraints: On Monday, Tyler avoids meetings before 16:00 (960 minutes)
    min_start_per_day = {
        'Monday': 960,  # 16:00
        'Tuesday': work_start,
        'Wednesday': work_start
    }

    # Iterate through each day
    for day in days:
        min_start = min_start_per_day[day]
        # Combine busy intervals for both participants
        busy_intervals = tyler_busy.get(day, []) + ruth_busy.get(day, [])
        if not busy_intervals:
            # Entire work day is free
            free_intervals = [(work_start, work_end)]
        else:
            # Sort intervals by start time
            busy_intervals.sort(key=lambda x: x[0])
            merged_busy = []
            start, end = busy_intervals[0]
            # Merge overlapping intervals
            for interval in busy_intervals[1:]:
                s, e = interval
                if s <= end:
                    end = max(end, e)
                else:
                    merged_busy.append((start, end))
                    start, end = s, e
            merged_busy.append((start, end))
            
            # Compute free intervals within work hours
            free_intervals = []
            current = work_start
            for s, e in merged_busy:
                if current < s:
                    free_intervals.append((current, s))
                current = max(current, e)
            if current < work_end:
                free_intervals.append((current, work_end))
        
        # Check each free interval for a suitable meeting slot
        for start_free, end_free in free_intervals:
            candidate_start = max(start_free, min_start)
            if candidate_start + meeting_duration <= end_free:
                # Convert start time to HH:MM format
                start_hour = candidate_start // 60
                start_min = candidate_start % 60
                # Calculate end time
                end_time = candidate_start + meeting_duration
                end_hour = end_time // 60
                end_min = end_time % 60
                # Format the time range as HH:MM:HH:MM
                time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
                print(f"{day} {time_str}")
                return
    
    # If no slot found (though problem states there is a solution)
    print("No suitable time found")

if __name__ == "__main__":
    main()