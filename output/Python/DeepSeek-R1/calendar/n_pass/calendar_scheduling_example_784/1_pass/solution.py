def main():
    # Convert time string to minutes since midnight
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        return int(parts[0]) * 60 + int(parts[1])
    
    # Convert minutes back to HH:MM format
    def minutes_to_time(m):
        hours = m // 60
        minutes = m % 60
        return f"{hours:02d}:{minutes:02d}"
    
    # Define work hours in minutes
    work_start = time_to_minutes('9:00')  # 540 minutes
    work_end = time_to_minutes('17:00')   # 1020 minutes
    
    # Busy intervals for each participant per day in minutes
    busy_times = {
        'Monday': {
            'Judith': [(time_to_minutes('12:00'), time_to_minutes('12:30'))],
            'Timothy': [
                (time_to_minutes('9:30'), time_to_minutes('10:00')),
                (time_to_minutes('10:30'), time_to_minutes('11:30')),
                (time_to_minutes('12:30'), time_to_minutes('14:00')),
                (time_to_minutes('15:30'), time_to_minutes('17:00'))
            ]
        },
        'Tuesday': {
            'Judith': [],
            'Timothy': [
                (time_to_minutes('9:30'), time_to_minutes('13:00')),
                (time_to_minutes('13:30'), time_to_minutes('14:00')),
                (time_to_minutes('14:30'), time_to_minutes('17:00'))
            ]
        },
        'Wednesday': {
            'Judith': [(time_to_minutes('11:30'), time_to_minutes('12:00'))],
            'Timothy': [
                (time_to_minutes('9:00'), time_to_minutes('9:30')),
                (time_to_minutes('10:30'), time_to_minutes('11:00')),
                (time_to_minutes('13:30'), time_to_minutes('14:30')),
                (time_to_minutes('15:00'), time_to_minutes('15:30')),
                (time_to_minutes('16:00'), time_to_minutes('16:30'))
            ]
        }
    }
    
    # Define segments in order of preference
    segments = [
        ('Tuesday', work_start, work_end),
        ('Wednesday', time_to_minutes('12:00'), work_end),
        ('Wednesday', work_start, time_to_minutes('12:00')),
        ('Monday', work_start, work_end)
    ]
    
    meeting_duration = 60  # minutes
    found = False
    slot_start_minutes = None
    chosen_day = None
    
    for segment in segments:
        day, seg_start, seg_end = segment
        busy_intervals = []
        
        # Collect Judith's busy intervals in the segment
        for interval in busy_times[day]['Judith']:
            low = max(interval[0], seg_start)
            high = min(interval[1], seg_end)
            if low < high:
                busy_intervals.append((low, high))
        
        # Collect Timothy's busy intervals in the segment
        for interval in busy_times[day]['Timothy']:
            low = max(interval[0], seg_start)
            high = min(interval[1], seg_end)
            if low < high:
                busy_intervals.append((low, high))
        
        # Sort intervals by start time
        busy_intervals.sort(key=lambda x: x[0])
        
        # Merge overlapping intervals
        merged = []
        if busy_intervals:
            current_start, current_end = busy_intervals[0]
            for i in range(1, len(busy_intervals)):
                s, e = busy_intervals[i]
                if s <= current_end:
                    current_end = max(current_end, e)
                else:
                    merged.append((current_start, current_end))
                    current_start, current_end = s, e
            merged.append((current_start, current_end))
        
        # Check for available slot
        if not merged:
            if seg_end - seg_start >= meeting_duration:
                slot_start_minutes = seg_start
                chosen_day = day
                found = True
                break
        else:
            # Check before first interval
            if merged[0][0] - seg_start >= meeting_duration:
                slot_start_minutes = seg_start
                chosen_day = day
                found = True
                break
            
            # Check between intervals
            for i in range(len(merged) - 1):
                gap_start = merged[i][1]
                gap_end = merged[i+1][0]
                if gap_end - gap_start >= meeting_duration:
                    slot_start_minutes = gap_start
                    chosen_day = day
                    found = True
                    break
            if found:
                break
                
            # Check after last interval
            if seg_end - merged[-1][1] >= meeting_duration:
                slot_start_minutes = merged[-1][1]
                chosen_day = day
                found = True
                break
    
    if found:
        start_hour = slot_start_minutes // 60
        start_min = slot_start_minutes % 60
        end_minutes = slot_start_minutes + meeting_duration
        end_hour = end_minutes // 60
        end_min = end_minutes % 60
        time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
        print(chosen_day)
        print(time_str)
    else:
        # According to the problem, a solution exists, so this should not happen.
        print("No suitable slot found")

if __name__ == '__main__':
    main()