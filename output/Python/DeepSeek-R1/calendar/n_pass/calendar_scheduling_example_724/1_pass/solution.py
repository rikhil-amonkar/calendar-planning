def main():
    work_start = 540  # 9:00 in minutes from midnight
    work_end = 1020   # 17:00 in minutes from midnight
    duration = 30     # meeting duration in minutes

    # Define busy intervals for Tyler and Ruth
    tyler_busy = {
        'Monday': [(540, 960)],   # Avoid before 16:00 (16:00=960 minutes)
        'Tuesday': [(540, 570), (870, 900)],  # 9:00-9:30, 14:30-15:00
        'Wednesday': [(630, 660), (750, 780), (810, 840), (990, 1020)]  # 10:30-11:00, 12:30-13:00, 13:30-14:00, 16:30-17:00
    }
    
    ruth_busy = {
        'Monday': [(540, 600), (630, 720), (750, 870), (900, 960), (990, 1020)],  # Given blocks
        'Tuesday': [(540, 1020)],  # Entire day
        'Wednesday': [(540, 1020)]   # Entire day
    }
    
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    for day in days:
        # Combine busy intervals for the day
        busy = tyler_busy.get(day, []) + ruth_busy.get(day, [])
        if not busy:
            # Entire day free? Use first available slot
            free_intervals = [(work_start, work_end)]
        else:
            # Sort by start time
            busy_sorted = sorted(busy, key=lambda x: x[0])
            merged = []
            start_curr, end_curr = busy_sorted[0]
            for i in range(1, len(busy_sorted)):
                s, e = busy_sorted[i]
                if s <= end_curr:
                    end_curr = max(end_curr, e)
                else:
                    merged.append((start_curr, end_curr))
                    start_curr, end_curr = s, e
            merged.append((start_curr, end_curr))
            
            # Compute free intervals
            free_intervals = []
            current = work_start
            for interval in merged:
                s, e = interval
                if current < s:
                    free_intervals.append((current, s))
                current = max(current, e)
            if current < work_end:
                free_intervals.append((current, work_end))
        
        # Check free intervals for sufficient duration
        for interval in free_intervals:
            start_free, end_free = interval
            if end_free - start_free >= duration:
                meeting_start = start_free
                meeting_end = meeting_start + duration
                # Format times
                start_hr = meeting_start // 60
                start_min = meeting_start % 60
                end_hr = meeting_end // 60
                end_min = meeting_end % 60
                time_str = f"{start_hr}:{start_min:02d}:{end_hr}:{end_min:02d}"
                print(day)
                print(time_str)
                return
                
    print("No suitable time found")

if __name__ == "__main__":
    main()