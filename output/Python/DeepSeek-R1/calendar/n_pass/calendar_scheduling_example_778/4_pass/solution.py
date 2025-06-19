def main():
    # Define preferred day order: Monday, Wednesday, Tuesday (avoid Tuesday if possible)
    days_order = ['Monday', 'Wednesday', 'Tuesday']
    
    # Available time windows (minutes from 9:00) as half-open intervals [start, end)
    available_time = {
        'Monday': (0, 420),    # 9:00-16:00 (7 hours)
        'Tuesday': (0, 480),   # 9:00-17:00 (8 hours)
        'Wednesday': (0, 480)  # 9:00-17:00
    }
    
    # Susan's schedule
    susan_schedule = {
        'Monday': ["12:30 to 13:00", "13:30 to 14:00"],
        'Tuesday': ["11:30 to 12:00"],
        'Wednesday': ["9:30 to 10:30", "14:00 to 14:30", "15:30 to 16:30"]
    }
    
    # Sandra's schedule
    sandra_schedule = {
        'Monday': ["9:00 to 13:00", "14:00 to 15:00", "16:00 to 16:30"],
        'Tuesday': ["9:00 to 9:30", "10:30 to 12:00", "12:30 to 13:30", "14:00 to 14:30", "16:00 to 17:00"],
        'Wednesday': ["9:00 to 11:30", "12:00 to 12:30", "13:00 to 17:00"]
    }
    
    # Convert time string to minutes from 9:00
    def time_str_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return (hour - 9) * 60 + minute

    # Parse interval string into (start_minutes, end_minutes)
    def parse_interval(interval_str):
        start_str, end_str = interval_str.split(' to ')
        return (
            time_str_to_minutes(start_str.strip()),
            time_str_to_minutes(end_str.strip())
        )

    # Merge overlapping intervals
    def merge_intervals(intervals):
        if not intervals:
            return []
        sorted_intervals = sorted(intervals, key=lambda x: x[0])
        merged = []
        current_start, current_end = sorted_intervals[0]
        for s, e in sorted_intervals[1:]:
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))
        return merged

    # Find free intervals within availability window
    def find_free_intervals(busy_intervals, available_start, available_end):
        merged_busy = merge_intervals(busy_intervals)
        free = []
        current = available_start
        for s, e in merged_busy:
            if current < s:
                free.append((current, s))
            current = max(current, e)
        if current < available_end:
            free.append((current, available_end))
        return free

    # Convert minutes back to "HH:MM" format
    def minutes_to_time(minutes):
        hour = 9 + minutes // 60
        minute = minutes % 60
        return f"{hour:02d}:{minute:02d}"

    # Find all valid meeting slots
    valid_slots = []
    for day in days_order:
        available_start, available_end = available_time[day]
        busy_intervals = []

        # Add Susan's busy intervals (clipped to availability)
        if day in susan_schedule:
            for interval in susan_schedule[day]:
                s, e = parse_interval(interval)
                s = max(s, available_start)
                e = min(e, available_end)
                if s < e:
                    busy_intervals.append((s, e))

        # Add Sandra's busy intervals (clipped to availability)
        if day in sandra_schedule:
            for interval in sandra_schedule[day]:
                s, e = parse_interval(interval)
                s = max(s, available_start)
                e = min(e, available_end)
                if s < e:
                    busy_intervals.append((s, e))

        # Calculate free intervals
        free_intervals = find_free_intervals(busy_intervals, available_start, available_end)

        # Check each free interval for 30-minute slots
        for start, end in free_intervals:
            duration = end - start
            if duration >= 30:
                # Slot can start at beginning of free interval
                slot_start = start
                slot_end = start + 30
                # Format slot details
                start_time = minutes_to_time(slot_start)
                end_time = minutes_to_time(slot_end)
                valid_slots.append((day, f"{start_time} to {end_time}"))

    # Select earliest chronological slot
    if valid_slots:
        # Sort by day order then time
        day_priority = {day: idx for idx, day in enumerate(days_order)}
        valid_slots.sort(key=lambda x: (day_priority[x[0]], x[1]))
        day, time_slot = valid_slots[0]
        print(day)
        print(time_slot)
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()