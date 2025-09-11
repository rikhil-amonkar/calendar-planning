def main():
    # Convert time string to minutes since 00:00 for easier calculation
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes

    # Convert minutes since 00:00 back to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    # Work hours: 9:00 to 17:00 (40800 to 61200 in minutes since 00:00)
    work_start = time_to_minutes('09:00')
    work_end = time_to_minutes('17:00')
    meeting_duration = 60  # minutes

    # Russell's constraints
    russell_busy = {
        'Monday': [('10:30', '11:00')],
        'Tuesday': [('13:00', '13:30')]
    }
    # Russell's preference: not before 13:30 on Tuesday
    tuesday_preference_start = time_to_minutes('13:30')

    # Alexander's constraints
    alexander_busy = {
        'Monday': [('09:00', '11:30'), ('12:00', '14:30'), ('15:00', '17:00')],
        'Tuesday': [('09:00', '10:00'), ('13:00', '14:00'), ('15:00', '15:30'), ('16:00', '16:30')]
    }

    days = ['Monday', 'Tuesday']
    for day in days:
        # Combine and convert busy intervals to minutes
        busy_intervals = []
        for person_busy in [russell_busy, alexander_busy]:
            if day in person_busy:
                for start, end in person_busy[day]:
                    start_min = time_to_minutes(start)
                    end_min = time_to_minutes(end)
                    busy_intervals.append((start_min, end_min))
        
        # Sort intervals by start time
        busy_intervals.sort(key=lambda x: x[0])
        
        # Merge overlapping intervals
        merged = []
        for start, end in busy_intervals:
            if not merged or start > merged[-1][1]:
                merged.append([start, end])
            else:
                merged[-1][1] = max(merged[-1][1], end)
        
        # Find free slots within work hours
        free_slots = []
        current_start = work_start
        for busy_start, busy_end in merged:
            if current_start < busy_start:
                free_slots.append((current_start, busy_start))
            current_start = max(current_start, busy_end)
        if current_start < work_end:
            free_slots.append((current_start, work_end))
        
        # Check each free slot for availability and duration
        for slot_start, slot_end in free_slots:
            slot_duration = slot_end - slot_start
            if slot_duration >= meeting_duration:
                candidate_start = slot_start
                candidate_end = candidate_start + meeting_duration
                # On Tuesday, respect Russell's preference
                if day == 'Tuesday' and candidate_start < tuesday_preference_start:
                    continue
                # Ensure the candidate slot doesn't exceed the free slot
                if candidate_end <= slot_end:
                    # Format the output
                    start_time_str = minutes_to_time(candidate_start)
                    end_time_str = minutes_to_time(candidate_end)
                    print(f"{day} {start_time_str}:{end_time_str}")
                    return
    
    print("No suitable time found")

if __name__ == "__main__":
    main()