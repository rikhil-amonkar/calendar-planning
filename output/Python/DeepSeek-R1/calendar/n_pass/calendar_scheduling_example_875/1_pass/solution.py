def main():
    # Work day: 9:00 to 17:00 represented in minutes from 9:00 (0 to 480 minutes)
    work_day_start = 0
    work_day_end = 480  # 17:00 is 8 hours after 9:00 (8*60=480)
    meeting_duration = 60  # 1 hour

    # Days to consider
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

    # Hard-coded busy intervals for Natalie and William (in minutes from 9:00)
    natalie_busy = {
        'Monday': [(0, 30), (60, 180), (210, 240), (300, 330), (360, 450)],
        'Tuesday': [(0, 30), (60, 90), (210, 300), (420, 480)],
        'Wednesday': [(120, 150), (420, 450)],
        'Thursday': [(60, 120), (150, 360), (390, 420), (450, 480)]
    }

    william_busy = {
        'Monday': [(30, 120), (150, 480)],
        'Tuesday': [(0, 240), (270, 420)],
        'Wednesday': [(0, 210), (240, 330), (390, 420), (450, 480)],
        'Thursday': [(0, 90), (120, 150), (180, 210), (240, 300), (360, 480)]
    }

    # Function to merge intervals and compute free intervals
    def get_free_intervals(busy_intervals, total_start, total_end):
        if not busy_intervals:
            return [(total_start, total_end)]
        # Sort by start time
        sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
        merged = []
        start, end = sorted_busy[0]
        for i in range(1, len(sorted_busy)):
            s, e = sorted_busy[i]
            if s <= end:
                if e > end:
                    end = e
            else:
                merged.append((start, end))
                start, end = s, e
        merged.append((start, end))
        
        free = []
        current = total_start
        for s, e in merged:
            if current < s:
                free.append((current, s))
            current = e
        if current < total_end:
            free.append((current, total_end))
        return free

    # Iterate over days to find a suitable meeting time
    found = False
    for day in days:
        # Get free intervals for Natalie and William
        natalie_free = get_free_intervals(natalie_busy.get(day, []), work_day_start, work_day_end)
        william_free = get_free_intervals(william_busy.get(day, []), work_day_start, work_day_end)
        
        # Find overlapping free intervals of at least meeting_duration
        i = j = 0
        while i < len(natalie_free) and j < len(william_free):
            n_start, n_end = natalie_free[i]
            w_start, w_end = william_free[j]
            
            # Calculate overlap
            low = max(n_start, w_start)
            high = min(n_end, w_end)
            if low < high:  # There is an overlap
                if high - low >= meeting_duration:
                    # Found a slot: use the earliest possible start (low) to low+meeting_duration
                    start_minutes = low
                    end_minutes = low + meeting_duration
                    
                    # Convert minutes to time strings (HH:MM)
                    start_hour = 9 + start_minutes // 60
                    start_minute = start_minutes % 60
                    end_hour = 9 + end_minutes // 60
                    end_minute = end_minutes % 60
                    
                    # Format time strings with leading zeros for minutes
                    start_str = f"{start_hour}:{start_minute:02d}"
                    end_str = f"{end_hour}:{end_minute:02d}"
                    time_str = f"{start_str}:{end_str}"
                    
                    # Output the day and time string
                    print(day)
                    print(time_str)
                    found = True
                    break
            # Move pointers based on which free interval ends first
            if n_end < w_end:
                i += 1
            else:
                j += 1
        if found:
            break

if __name__ == "__main__":
    main()