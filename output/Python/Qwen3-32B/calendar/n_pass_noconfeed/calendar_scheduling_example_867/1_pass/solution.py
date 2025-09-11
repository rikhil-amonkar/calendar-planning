def main():
    # Define busy times in minutes since midnight
    betty_busy = {
        'Monday': [(10*60, 10*60+30), (13*60+30, 14*60), (15*60, 15*60+30), (16*60, 16*60+30)],
        'Tuesday': [(9*60, 9*60+30), (11*60+30, 12*60), (12*60+30, 13*60), (13*60+30, 14*60), (16*60+30, 17*60)],
        'Wednesday': [(9*60+30, 10*60+30), (13*60, 13*60+30), (14*60, 14*60+30)],
        'Thursday': [(9*60+30, 10*60), (11*60+30, 12*60), (14*60, 14*60+30), (15*60, 15*60+30), (16*60+30, 17*60)]
    }
    
    scott_busy = {
        'Monday': [(9*60+30, 15*60), (15*60+30, 16*60), (16*60+30, 17*60)],
        'Tuesday': [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 12*60), (12*60+30, 13*60+30), (14*60, 15*60), (16*60, 16*60+30)],
        'Wednesday': [(9*60+30, 12*60+30), (13*60, 13*60+30), (14*60, 14*60+30), (15*60, 15*60+30), (16*60, 16*60+30)],
        'Thursday': [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 12*60), (12*60+30, 13*60), (15*60, 16*60), (16*60+30, 17*60)]
    }
    
    def get_free_intervals(busy_intervals, constraint_start=None):
        sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
        free = []
        prev_end = 9*60  # 9:00 AM
        for start, end in sorted_busy:
            if prev_end < start:
                free.append((prev_end, start))
            prev_end = max(prev_end, end)
        if prev_end < 17*60:  # 5:00 PM
            free.append((prev_end, 17*60))
        # Apply constraint if any
        if constraint_start is not None:
            constrained_free = []
            for start, end in free:
                new_start = max(start, constraint_start)
                if new_start < end:
                    constrained_free.append((new_start, end))
            return constrained_free
        else:
            return free
    
    def find_overlaps(intervals1, intervals2, min_duration=30):
        overlaps = []
        for (s1, e1) in intervals1:
            for (s2, e2) in intervals2:
                start = max(s1, s2)
                end = min(e1, e2)
                if start < end:
                    duration = end - start
                    if duration >= min_duration:
                        overlaps.append((start, end))
        return overlaps
    
    allowed_days_order = [
        ('Tuesday', 15*60),  # 15:00
        ('Thursday', 15*60),
        ('Wednesday', None)
    ]
    
    for day, constraint in allowed_days_order:
        betty_day_busy = betty_busy.get(day, [])
        scott_day_busy = scott_busy.get(day, [])
        
        # Get Betty's free intervals with constraint
        betty_free = get_free_intervals(betty_day_busy, constraint)
        # Get Scott's free intervals (no constraint)
        scott_free = get_free_intervals(scott_day_busy, None)
        
        # Find overlaps
        overlaps = find_overlaps(betty_free, scott_free)
        if overlaps:
            # Pick earliest start
            earliest = min(overlaps, key=lambda x: x[0])
            meeting_start = earliest[0]
            meeting_end = meeting_start + 30  # 30 minutes meeting
            # Convert to time format
            def to_time(mins):
                h = mins // 60
                m = mins % 60
                return f"{h:02d}:{m:02d}"
            start_time = to_time(meeting_start)
            end_time = to_time(meeting_end)
            print(f"{day} {start_time}:{end_time}")
            return
    
    # If no day found (should not happen per problem statement)
    print("No suitable time found")

if __name__ == "__main__":
    main()