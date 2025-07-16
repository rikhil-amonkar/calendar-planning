def main():
    # Convert time to minutes from start of day (9:00 AM = 540 minutes, 5:00 PM = 1020 minutes)
    work_start = 9 * 60
    work_end = 17 * 60
    meeting_duration = 60  # 60 minutes

    # Define the schedules for each participant per day (busy intervals as [start, end) in minutes)
    schedules = {
        'Bryan': {
            'Wednesday': [],
            'Friday': [(10*60+30, 11*60), (14*60, 14*60+30)]  # 10:30-11:00, 14:00-14:30
        },
        'Nicholas': {
            'Wednesday': [
                (9*60, 9*60+30),        # 9:00-9:30
                (10*60, 11*60),          # 10:00-11:00
                (11*60+30, 13*60+30),    # 11:30-13:30
                (14*60, 14*60+30),       # 14:00-14:30
                (15*60, 16*60+30)        # 15:00-16:30
            ],
            'Friday': [
                (9*60, 10*60+30),       # 9:00-10:30
                (11*60, 12*60),         # 11:00-12:00
                (12*60+30, 14*60+30),   # 12:30-14:30
                (15*60+30, 16*60),      # 15:30-16:00
                (16*60+30, 17*60)       # 16:30-17:00
            ]
        }
    }

    # Days to consider (avoid Tuesday for Bryan, Monday/Thursday for Nicholas -> only Wed/Fri)
    days = ['Wednesday', 'Friday']

    # Iterate through each day to find a slot
    for day in days:
        busy_intervals = []
        # Collect all busy intervals for the day from both participants
        for participant in schedules:
            busy_intervals.extend(schedules[participant][day])
        
        # If no meetings, the entire day is free
        if not busy_intervals:
            # Check if the work day has enough time
            if work_end - work_start >= meeting_duration:
                start_min = work_start
                end_min = work_start + meeting_duration
                # Format and output
                print(day)
                print(f"{start_min//60:02d}:{start_min%60:02d}:{end_min//60:02d}:{end_min%60:02d}")
                return
        
        # Sort busy intervals by start time
        busy_intervals.sort()
        merged = []
        start_curr, end_curr = busy_intervals[0]
        # Merge overlapping or adjacent intervals
        for i in range(1, len(busy_intervals)):
            s, e = busy_intervals[i]
            if s <= end_curr:  # Overlapping or adjacent
                if e > end_curr:
                    end_curr = e
            else:
                merged.append((start_curr, end_curr))
                start_curr, end_curr = s, e
        merged.append((start_curr, end_curr))
        
        # Find free intervals
        free_intervals = []
        current = work_start
        for interval in merged:
            s, e = interval
            if current < s:  # Free interval before this busy period
                free_intervals.append((current, s))
            current = max(current, e)
        if current < work_end:  # Free interval after last busy period
            free_intervals.append((current, work_end))
        
        # Check each free interval for sufficient duration
        for interval in free_intervals:
            start_free, end_free = interval
            duration = end_free - start_free
            if duration >= meeting_duration:
                start_min = start_free
                end_min = start_free + meeting_duration
                # Format and output
                print(day)
                print(f"{start_min//60:02d}:{start_min%60:02d}:{end_min//60:02d}:{end_min%60:02d}")
                return

if __name__ == "__main__":
    main()