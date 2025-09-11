def find_meeting_time():
    # Define busy times in minutes since midnight
    busy_schedule = {
        'Monday': [
            (540, 660),   # 9:00-11:00
            (690, 780),   # 11:30-13:00
            (810, 870),   # 13:30-14:30
            (900, 1020),  # 15:00-17:00
        ],
        'Tuesday': [
            (540, 690),   # 9:00-11:30
            (720, 1020),  # 12:00-17:00
        ],
        'Wednesday': [
            (540, 690),   # 9:00-11:30
            (720, 750),   # 12:00-12:30
            (780, 840),   # 13:00-14:00
            (870, 960),   # 14:30-16:00
            (990, 1020),  # 16:30-17:00
        ],
    }

    work_start = 540  # 9:00 AM
    work_end = 1020   # 5:00 PM

    for day in ['Tuesday', 'Wednesday', 'Monday']:
        busy_intervals = busy_schedule.get(day, [])
        # Sort intervals by start time (already sorted in this case)
        busy_intervals.sort()
        # Generate free slots
        prev_end = work_start
        for interval in busy_intervals:
            start, end = interval
            # Free slot between prev_end and start
            if start > prev_end:
                free_start = prev_end
                free_end = start
                if free_end - free_start >= 30:
                    # Check if it's Monday and after 14:30 (870 minutes)
                    if day == 'Monday' and free_start >= 870:
                        continue  # John's constraint
                    # Found a valid slot
                    return format_slot(free_start, free_end, day)
            # Update prev_end
            prev_end = end
        # Check after last busy interval
        if work_end > prev_end:
            free_start = prev_end
            free_end = work_end
            if free_end - free_start >= 30:
                if day == 'Monday' and free_start >= 870:
                    continue
                return format_slot(free_start, free_end, day)
    # If no slot found (but problem says there is a solution)
    return "No solution found"

def format_slot(start_min, end_min, day):
    # Convert minutes to HH:MM format
    def to_time(mins):
        hours = mins // 60
        minutes = mins % 60
        return f"{hours:02d}:{minutes:02d}"
    start_time = to_time(start_min)
    end_time = to_time(end_min)
    return f"{day} {start_time}:{end_time}"

print(find_meeting_time())