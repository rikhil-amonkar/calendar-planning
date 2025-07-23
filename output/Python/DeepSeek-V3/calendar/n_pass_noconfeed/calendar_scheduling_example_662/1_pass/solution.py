def find_meeting_time(gary_schedule, david_schedule, days, work_hours, duration):
    for day in days:
        # Initialize available time for the day
        start_work, end_work = work_hours
        available_start = start_work
        
        # Combine and sort all busy intervals for both participants
        busy_intervals = gary_schedule.get(day, []) + david_schedule.get(day, [])
        busy_intervals.sort()
        
        # Merge overlapping or adjacent intervals
        merged = []
        for start, end in busy_intervals:
            if not merged:
                merged.append([start, end])
            else:
                last_start, last_end = merged[-1]
                if start <= last_end:
                    merged[-1] = [last_start, max(last_end, end)]
                else:
                    merged.append([start, end])
        
        # Check available slots
        for busy_start, busy_end in merged:
            if available_start < busy_start:
                slot_start = available_start
                slot_end = busy_start
                if (slot_end - slot_start) >= duration:
                    return day, (slot_start, slot_start + duration)
            available_start = max(available_start, busy_end)
        
        # Check after last busy interval
        if (end_work - available_start) >= duration:
            return day, (available_start, available_start + duration)
    
    return None, None

def main():
    # Define work hours and meeting duration
    work_hours = (9 * 60, 17 * 60)  # 9:00 to 17:00 in minutes
    duration = 60  # 1 hour in minutes
    days = ['Monday', 'Tuesday']
    
    # Define schedules in minutes since midnight
    gary_schedule = {
        'Monday': [
            (9 * 60 + 30, 10 * 60),
            (11 * 60, 13 * 60),
            (14 * 60, 14 * 60 + 30),
            (16 * 60 + 30, 17 * 60)
        ],
        'Tuesday': [
            (9 * 60, 9 * 60 + 30),
            (10 * 60 + 30, 11 * 60),
            (14 * 60 + 30, 16 * 60)
        ]
    }
    
    david_schedule = {
        'Monday': [
            (9 * 60, 9 * 60 + 30),
            (10 * 60, 13 * 60),
            (14 * 60 + 30, 16 * 60 + 30)
        ],
        'Tuesday': [
            (9 * 60, 9 * 60 + 30),
            (10 * 60, 10 * 60 + 30),
            (11 * 60, 12 * 60 + 30),
            (13 * 60, 14 * 60 + 30),
            (15 * 60, 16 * 60),
            (16 * 60 + 30, 17 * 60)
        ]
    }
    
    day, (start, end) = find_meeting_time(gary_schedule, david_schedule, days, work_hours, duration)
    
    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_time = minutes_to_time(start)
    end_time = minutes_to_time(end)
    
    print(f"{day}: {start_time}:{end_time}")

if __name__ == "__main__":
    main()