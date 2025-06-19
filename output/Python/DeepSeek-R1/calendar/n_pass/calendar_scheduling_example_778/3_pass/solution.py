def main():
    # Define the preferred order of days: Monday, Wednesday, Tuesday (to avoid Tuesday if possible)
    days_order = ['Monday', 'Wednesday', 'Tuesday']
    
    # Available time windows in minutes (from 0 at 9:00) as half-open intervals [start, end)
    available_time = {
        'Monday': (0, 420),    # 9:00 to 16:00 (7 hours = 420 minutes)
        'Tuesday': (0, 480),   # 9:00 to 17:00 (8 hours = 480 minutes)
        'Wednesday': (0, 480)
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
    
    # Helper function to convert time string to minutes from 9:00
    def time_str_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return (hour - 9) * 60 + minute
    
    # Helper function to parse an interval string
    def parse_interval(interval_str):
        parts = interval_str.split(' to ')
        start_str = parts[0].strip()
        end_str = parts[1].strip()
        return (time_str_to_minutes(start_str), time_str_to_minutes(end_str))
    
    # Helper function to merge overlapping intervals
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
    
    # Helper function to find free intervals given busy intervals and available window
    def find_free_intervals(busy_intervals, available_start, available_end):
        if not busy_intervals:
            return [(available_start, available_end)]
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
    
    # Helper function to convert minutes back to time string (HH:MM)
    def minutes_to_time(minutes):
        total_minutes = minutes
        hour = 9 + total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    # Iterate through each day in the preferred order
    for day in days_order:
        available_start, available_end = available_time[day]
        busy_intervals = []
        
        # Process Susan's schedule for the day
        if day in susan_schedule:
            for interval in susan_schedule[day]:
                s, e = parse_interval(interval)
                # Clip the interval to the available time window
                s_clip = max(s, available_start)
                e_clip = min(e, available_end)
                if s_clip < e_clip:
                    busy_intervals.append((s_clip, e_clip))
        
        # Process Sandra's schedule for the day
        if day in sandra_schedule:
            for interval in sandra_schedule[day]:
                s, e = parse_interval(interval)
                s_clip = max(s, available_start)
                e_clip = min(e, available_end)
                if s_clip < e_clip:
                    busy_intervals.append((s_clip, e_clip))
        
        # Find free intervals
        free_intervals = find_free_intervals(busy_intervals, available_start, available_end)
        
        # Check each free interval for a 30-minute slot
        for start, end in free_intervals:
            duration = end - start
            if duration >= 30:
                # Schedule the meeting at the beginning of the free interval
                meeting_start = start
                meeting_end = start + 30
                # Convert to time strings
                start_time_str = minutes_to_time(meeting_start)
                end_time_str = minutes_to_time(meeting_end)
                # Format the output as "HH:MM to HH:MM"
                time_output = f"{start_time_str} to {end_time_str}"
                print(day)
                print(time_output)
                return
    
    # If no slot is found (though the problem guarantees a solution)
    print("No suitable time found")

if __name__ == "__main__":
    main()