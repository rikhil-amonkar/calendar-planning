def main():
    # Define work hours (9:00 to 17:00) in minutes
    work_start = 9 * 60  # 540 minutes
    work_end = 17 * 60   # 1020 minutes

    # Days to consider
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

    # Busy intervals in minutes for each participant per day
    mary_busy = {
        'Tuesday': [(10*60, 10*60+30), (15*60+30, 16*60)],
        'Wednesday': [(9*60+30, 10*60), (15*60, 15*60+30)],
        'Thursday': [(9*60, 10*60), (10*60+30, 11*60+30)]
    }

    alexis_busy = {
        'Monday': [(9*60, 10*60), (10*60+30, 12*60), (12*60+30, 16*60+30)],
        'Tuesday': [(9*60, 10*60), (10*60+30, 11*60+30), (12*60, 15*60+30), (16*60, 17*60)],
        'Wednesday': [(9*60, 11*60), (11*60+30, 17*60)],
        'Thursday': [(10*60, 12*60), (14*60, 14*60+30), (15*60+30, 16*60), (16*60+30, 17*60)]
    }

    # Iterate over each day to find the earliest available slot
    for day in days:
        # Collect all busy intervals for this day
        busy_intervals = []
        
        # Add Mary's busy intervals if the day exists
        if day in mary_busy:
            busy_intervals.extend(mary_busy[day])
        
        # Add Alexis' busy intervals if the day exists
        if day in alexis_busy:
            busy_intervals.extend(alexis_busy[day])
        
        # If no busy intervals, the entire day is free -> schedule at 9:00
        if not busy_intervals:
            start_time = work_start
            end_time = start_time + 30
            # Format the time and output
            print(f"{day}")
            print(f"{start_time//60:02d}:{start_time%60:02d}:{end_time//60:02d}:{end_time%60:02d}")
            return
        
        # Sort busy intervals by start time
        busy_intervals.sort(key=lambda x: x[0])
        
        # Merge overlapping or adjacent intervals
        merged = []
        current_start, current_end = busy_intervals[0]
        for interval in busy_intervals[1:]:
            if interval[0] <= current_end:
                current_end = max(current_end, interval[1])
            else:
                merged.append((current_start, current_end))
                current_start, current_end = interval
        merged.append((current_start, current_end))
        
        # Find free intervals
        free_intervals = []
        current = work_start
        
        # Check before first meeting
        for start, end in merged:
            if current < start:
                free_intervals.append((current, start))
            current = max(current, end)
        
        # Check after last meeting
        if current < work_end:
            free_intervals.append((current, work_end))
        
        # Check each free interval for a 30-minute slot
        for start, end in free_intervals:
            if end - start >= 30:
                meeting_start = start
                meeting_end = start + 30
                # Format the time and output
                print(f"{day}")
                print(f"{meeting_start//60:02d}:{meeting_start%60:02d}:{meeting_end//60:02d}:{meeting_end%60:02d}")
                return

if __name__ == "__main__":
    main()