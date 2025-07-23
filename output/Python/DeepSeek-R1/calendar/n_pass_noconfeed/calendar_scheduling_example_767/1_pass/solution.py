def main():
    # Define work hours: 9:00 to 17:00
    work_start_min = 9 * 60   # 540 minutes
    work_end_min = 17 * 60    # 1020 minutes
    
    # Define schedules with blocked times
    schedules = {
        'Martha': {
            'Monday': [('16:00', '17:00')],
            'Tuesday': [('15:00', '15:30')],
            'Wednesday': [('10:00', '11:00'), ('14:00', '14:30')]
        },
        'Beverly': {
            'Monday': [('9:00', '13:30'), ('14:00', '17:00')],
            'Tuesday': [('9:00', '17:00')],
            'Wednesday': [('9:30', '15:30'), ('16:30', '17:00')]
        }
    }
    
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Helper function to convert time string to minutes
    def time_str_to_minutes(time_str):
        parts = time_str.split(':')
        return int(parts[0]) * 60 + int(parts[1])
    
    # Helper function to convert minutes to HH:MM string
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    # Function to subtract a blocked interval from free intervals
    def subtract_blocked_interval(free_intervals, blocked):
        new_free = []
        b_start, b_end = blocked
        for interval in free_intervals:
            s, e = interval
            if b_end <= s or b_start >= e:
                new_free.append([s, e])
            else:
                if s < b_start:
                    new_free.append([s, b_start])
                if b_end < e:
                    new_free.append([b_end, e])
        return new_free
    
    # Function to compute intersection of two sets of intervals
    def intersect_intervals(intervals1, intervals2):
        i = j = 0
        common = []
        while i < len(intervals1) and j < len(intervals2):
            s1, e1 = intervals1[i]
            s2, e2 = intervals2[j]
            low = max(s1, s2)
            high = min(e1, e2)
            if low < high:
                common.append([low, high])
            if e1 < e2:
                i += 1
            else:
                j += 1
        return common
    
    # Iterate over days to find a suitable meeting time
    found = False
    for day in days:
        # Get blocked intervals for Martha and convert to minutes
        martha_blocks = schedules['Martha'].get(day, [])
        martha_blocks_min = []
        for block in martha_blocks:
            start_min = time_str_to_minutes(block[0])
            end_min = time_str_to_minutes(block[1])
            martha_blocks_min.append((start_min, end_min))
        
        # Get blocked intervals for Beverly and convert to minutes
        beverly_blocks = schedules['Beverly'].get(day, [])
        beverly_blocks_min = []
        for block in beverly_blocks:
            start_min = time_str_to_minutes(block[0])
            end_min = time_str_to_minutes(block[1])
            beverly_blocks_min.append((start_min, end_min))
        
        # Compute free intervals for Martha
        martha_free = [[work_start_min, work_end_min]]
        for block in martha_blocks_min:
            martha_free = subtract_blocked_interval(martha_free, block)
        martha_free.sort(key=lambda x: x[0])
        
        # Compute free intervals for Beverly
        beverly_free = [[work_start_min, work_end_min]]
        for block in beverly_blocks_min:
            beverly_free = subtract_blocked_interval(beverly_free, block)
        beverly_free.sort(key=lambda x: x[0])
        
        # Find common free intervals
        common_free = intersect_intervals(martha_free, beverly_free)
        
        # Check for a slot of at least 60 minutes
        for interval in common_free:
            start_common, end_common = interval
            duration = end_common - start_common
            if duration >= 60:
                meeting_start = start_common
                meeting_end = meeting_start + 60
                
                # Convert times to strings and format output
                start_time_str = minutes_to_time(meeting_start)
                end_time_str = minutes_to_time(meeting_end)
                start_h, start_m = start_time_str.split(':')
                end_h, end_m = end_time_str.split(':')
                time_output = f"{start_h}:{start_m}:{end_h}:{end_m}"
                
                print(day)
                print(time_output)
                found = True
                return  # Exit after finding the first suitable slot
    
    # If no slot found (though problem states there is a solution)
    if not found:
        print("No suitable time found")

if __name__ == "__main__":
    main()