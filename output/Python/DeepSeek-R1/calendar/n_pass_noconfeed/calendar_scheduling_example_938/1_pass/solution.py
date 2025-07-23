def main():
    # Convert time string to minutes since midnight
    def time_to_minutes(time_str):
        h, m = time_str.split(':')
        return int(h) * 60 + int(m)
    
    # Convert minutes to HH:MM format
    def minutes_to_time(mins):
        h = mins // 60
        m = mins % 60
        return f"{h:02d}:{m:02d}"
    
    # Calculate free intervals given work hours and busy intervals
    def free_intervals(work_start, work_end, busy_intervals):
        free = [(work_start, work_end)]
        for b_start, b_end in busy_intervals:
            new_free = []
            for start, end in free:
                # No overlap
                if b_end <= start or b_start >= end:
                    new_free.append((start, end))
                else:
                    # Overlap: split the free interval
                    if start < b_start:
                        new_free.append((start, b_start))
                    if b_end < end:
                        new_free.append((b_end, end))
            free = new_free
        return free
    
    # Generate 30-minute slots within free intervals
    def free_slots(free_intervals_list):
        slots = []
        for start, end in free_intervals_list:
            current = start
            while current + 30 <= end:
                slots.append((current, current + 30))
                current += 30
        return slots
    
    # Work hours: 9:00 to 17:00 in minutes
    work_start = time_to_minutes('9:00')
    work_end = time_to_minutes('17:00')
    
    # Define busy times in minutes for each participant per day
    eugene_busy = {
        'Monday': [
            (time_to_minutes('11:00'), time_to_minutes('12:00')),
            (time_to_minutes('13:30'), time_to_minutes('14:00')),
            (time_to_minutes('14:30'), time_to_minutes('15:00')),
            (time_to_minutes('16:00'), time_to_minutes('16:30'))
        ],
        'Wednesday': [
            (time_to_minutes('9:00'), time_to_minutes('9:30')),
            (time_to_minutes('11:00'), time_to_minutes('11:30')),
            (time_to_minutes('12:00'), time_to_minutes('12:30')),
            (time_to_minutes('13:30'), time_to_minutes('15:00'))
        ],
        'Friday': [
            (time_to_minutes('10:30'), time_to_minutes('11:00')),
            (time_to_minutes('12:00'), time_to_minutes('12:30')),
            (time_to_minutes('13:00'), time_to_minutes('13:30'))
        ]
    }
    
    eric_busy = {
        'Monday': [
            (time_to_minutes('9:00'), time_to_minutes('17:00'))
        ],
        'Tuesday': [
            (time_to_minutes('9:00'), time_to_minutes('17:00'))
        ],
        'Wednesday': [
            (time_to_minutes('9:00'), time_to_minutes('11:30')),
            (time_to_minutes('12:00'), time_to_minutes('14:00')),
            (time_to_minutes('14:30'), time_to_minutes('16:30'))
        ],
        'Thursday': [
            (time_to_minutes('9:00'), time_to_minutes('17:00'))
        ],
        'Friday': [
            (time_to_minutes('9:00'), time_to_minutes('11:00')),
            (time_to_minutes('11:30'), time_to_minutes('17:00'))
        ]
    }
    
    # Days to try (avoid Wednesday if possible)
    candidate_days = ['Friday', 'Wednesday']
    
    for day in candidate_days:
        # Get free slots for Eugene
        eugene_intervals = free_intervals(work_start, work_end, eugene_busy.get(day, []))
        eugene_slots = free_slots(eugene_intervals)
        
        # Get free slots for Eric
        eric_intervals = free_intervals(work_start, work_end, eric_busy.get(day, []))
        eric_slots = free_slots(eric_intervals)
        
        # Find common free slots
        common_slots = set(eugene_slots) & set(eric_slots)
        if common_slots:
            # Choose the earliest slot
            slot = min(common_slots)
            start_min, end_min = slot
            # Format as HH:MM:HH:MM
            start_time = minutes_to_time(start_min)
            end_time = minutes_to_time(end_min)
            time_str = f"{start_time}:{end_time}".replace(':', ':', 2)
            print(time_str)
            print(day)
            return
    
    # Since a solution exists, this should not be reached
    print("No suitable time found")

if __name__ == "__main__":
    main()