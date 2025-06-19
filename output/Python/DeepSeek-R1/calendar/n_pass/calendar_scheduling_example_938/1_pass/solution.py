def main():
    # Define work hours (9:00 to 17:00) in minutes
    work_start = 9 * 60   # 540 minutes (9:00)
    work_end = 17 * 60    # 1020 minutes (17:00)
    meeting_duration = 30  # minutes

    # Busy times for Eugene (converted to minutes since midnight)
    eugene_busy = {
        'Monday': [('11:00', '12:00'), ('13:30', '14:00'), ('14:30', '15:00'), ('16:00', '16:30')],
        'Wednesday': [('9:00', '9:30'), ('11:00', '11:30'), ('12:00', '12:30'), ('13:30', '15:00')],
        'Thursday': [('9:30', '10:00'), ('11:00', '12:30')],
        'Friday': [('10:30', '11:00'), ('12:00', '12:30'), ('13:00', '13:30')]
    }
    
    # Busy times for Eric
    eric_busy = {
        'Monday': [('9:00', '17:00')],
        'Tuesday': [('9:00', '17:00')],
        'Wednesday': [('9:00', '11:30'), ('12:00', '14:00'), ('14:30', '16:30')],
        'Thursday': [('9:00', '17:00')],
        'Friday': [('9:00', '11:00'), ('11:30', '17:00')]
    }
    
    # Convert time strings to minutes
    def time_str_to_minutes(time_str):
        parts = time_str.split(':')
        return int(parts[0]) * 60 + int(parts[1])
    
    # Convert minutes to formatted time string (HH:MM)
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    # Function to calculate free intervals given busy intervals and work hours
    def calculate_free_intervals(busy_intervals, day):
        # If day not in busy_intervals, assume no busy times
        intervals = []
        if day in busy_intervals:
            for start_str, end_str in busy_intervals[day]:
                start_min = time_str_to_minutes(start_str)
                end_min = time_str_to_minutes(end_str)
                intervals.append((start_min, end_min))
        
        # Sort intervals by start time
        intervals.sort(key=lambda x: x[0])
        
        free = []
        current_start = work_start
        
        for start, end in intervals:
            if current_start < start:
                free.append((current_start, start))
            current_start = max(current_start, end)
        if current_start < work_end:
            free.append((current_start, work_end))
            
        return free
    
    # Function to find overlapping free intervals between two participants
    def find_common_free_intervals(free1, free2):
        common = []
        for start1, end1 in free1:
            for start2, end2 in free2:
                low = max(start1, start2)
                high = min(end1, end2)
                if low < high:
                    common.append((low, high))
        return common
    
    # Days to check (prioritize Friday to avoid Wednesday)
    days = ['Friday', 'Wednesday']
    result_day = None
    result_start = None
    
    for day in days:
        # Calculate free intervals for both participants
        eugene_free = calculate_free_intervals(eugene_busy, day)
        eric_free = calculate_free_intervals(eric_busy, day)
        
        # Find common free intervals
        common_free = find_common_free_intervals(eugene_free, eric_free)
        
        # Check for a slot of at least meeting_duration
        for start, end in common_free:
            if end - start >= meeting_duration:
                result_day = day
                result_start = start
                break
        if result_day:
            break
    
    # Format the result
    if result_day and result_start is not None:
        end_time = result_start + meeting_duration
        start_hour = result_start // 60
        start_min = result_start % 60
        end_hour = end_time // 60
        end_min = end_time % 60
        time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
        print(result_day)
        print(time_str)
    else:
        # Fallback: though problem states there is a solution
        print("No suitable time found")

if __name__ == "__main__":
    main()