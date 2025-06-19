def main():
    # Define work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
    work_start = 540
    work_end = 1020
    meeting_duration = 30  # minutes

    # Busy times for each participant per day (in minutes from midnight)
    busy_times = {
        'Monday': {
            'Joshua': [(15*60, 15*60 + 30)],  # 15:00-15:30
            'Joyce': [
                (9*60, 9*60 + 30),    # 9:00-9:30
                (10*60, 11*60),       # 10:00-11:00
                (11*60 + 30, 12*60 + 30),  # 11:30-12:30
                (13*60, 15*60),       # 13:00-15:00
                (15*60 + 30, 17*60)   # 15:30-17:00
            ]
        },
        'Tuesday': {
            'Joshua': [
                (11*60 + 30, 12*60),  # 11:30-12:00
                (13*60, 13*60 + 30),  # 13:00-13:30
                (14*60 + 30, 15*60)   # 14:30-15:00
            ],
            'Joyce': [(9*60, 17*60)]  # Entire day busy
        },
        'Wednesday': {
            'Joshua': [],  # No meetings
            'Joyce': [
                (9*60, 9*60 + 30),    # 9:00-9:30
                (10*60, 11*60),       # 10:00-11:00
                (12*60 + 30, 15*60 + 30),  # 12:30-15:30
                (16*60, 16*60 + 30)   # 16:00-16:30
            ]
        }
    }

    # Days to consider in order
    days = ['Monday', 'Tuesday', 'Wednesday']

    for day in days:
        # Skip Tuesday because Joyce is busy all day
        if day == 'Tuesday':
            continue
            
        # Combine busy intervals for both participants
        busy_intervals = []
        for participant in ['Joshua', 'Joyce']:
            busy_intervals.extend(busy_times[day][participant])
        
        # If no busy intervals, the entire day is free
        if not busy_intervals:
            merged_busy = []
            free_intervals = [(work_start, work_end)]
        else:
            # Sort and merge busy intervals
            busy_intervals.sort()
            merged_busy = []
            start, end = busy_intervals[0]
            for interval in busy_intervals[1:]:
                if interval[0] <= end:
                    end = max(end, interval[1])
                else:
                    merged_busy.append((start, end))
                    start, end = interval
            merged_busy.append((start, end))
            
            # Compute free intervals within work hours
            free_intervals = []
            current = work_start
            for s, e in merged_busy:
                if current < s:
                    free_intervals.append((current, s))
                current = e
            if current < work_end:
                free_intervals.append((current, work_end))
        
        # Check each free interval for a suitable slot
        for start_free, end_free in free_intervals:
            # On Monday, avoid times before 12:00 (720 minutes)
            if day == 'Monday':
                # Adjust start to at least 12:00
                slot_start = max(start_free, 12*60)
                slot_end = slot_start + meeting_duration
                if slot_end <= end_free:
                    # Convert to time string and output
                    start_hr, start_min = divmod(slot_start, 60)
                    end_hr, end_min = divmod(slot_end, 60)
                    time_str = f"{start_hr:02d}:{start_min:02d}:{end_hr:02d}:{end_min:02d}"
                    print(day)
                    print(time_str)
                    return
            else:
                # On Wednesday, any free slot of sufficient duration
                if end_free - start_free >= meeting_duration:
                    slot_start = start_free
                    slot_end = slot_start + meeting_duration
                    start_hr, start_min = divmod(slot_start, 60)
                    end_hr, end_min = divmod(slot_end, 60)
                    time_str = f"{start_hr:02d}:{start_min:02d}:{end_hr:02d}:{end_min:02d}"
                    print(day)
                    print(time_str)
                    return

if __name__ == "__main__":
    main()