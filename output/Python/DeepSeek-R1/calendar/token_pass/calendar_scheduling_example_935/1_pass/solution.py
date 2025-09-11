def main():
    # Define work hours in minutes from 9:00 (0) to 17:00 (480)
    work_start = 0
    work_end = 480
    meeting_duration = 30
    
    # Define days in order
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    
    # Define busy intervals for Terry and Frances for each day in minutes (start, end) with end exclusive
    terry_busy = {
        'Monday': [(90, 120), (210, 300), (360, 480)],
        'Tuesday': [(30, 60), (90, 120), (300, 330), (420, 450)],
        'Wednesday': [(30, 90), (120, 180), (240, 270), (360, 420), (450, 480)],
        'Thursday': [(30, 60), (180, 210), (240, 330), (420, 450)],
        'Friday': [(0, 150), (180, 210), (270, 420), (450, 480)]
    }
    
    frances_busy = {
        'Monday': [(30, 120), (150, 240), (300, 330), (360, 420)],
        'Tuesday': [(0, 30), (60, 90), (120, 180), (240, 330), (390, 450)],
        'Wednesday': [(30, 60), (90, 120), (150, 420), (450, 480)],
        'Thursday': [(120, 210), (330, 480)],
        'Friday': [(30, 90), (120, 210), (240, 420), (450, 480)]
    }
    
    # Iterate through days in order
    for day in days:
        # Get busy intervals for Terry and Frances for this day
        terry_busy_day = terry_busy[day]
        frances_busy_day = frances_busy[day]
        
        # Compute free intervals for Terry
        terry_free = compute_free_intervals(terry_busy_day, work_start, work_end)
        # Compute free intervals for Frances
        frances_free = compute_free_intervals(frances_busy_day, work_start, work_end)
        
        # Find common free intervals
        common_free = find_common_free_intervals(terry_free, frances_free)
        
        # Find the earliest start time S from common free intervals where interval length >= meeting_duration
        earliest_s = None
        for (a, b) in common_free:
            if b - a >= meeting_duration:
                if earliest_s is None or a < earliest_s:
                    earliest_s = a
        
        # If found a valid S, output and break
        if earliest_s is not None:
            # Convert S to time string
            start_hour = 9 + earliest_s // 60
            start_minute = earliest_s % 60
            end_time = earliest_s + meeting_duration
            end_hour = 9 + end_time // 60
            end_minute = end_time % 60
            
            # Format with leading zeros
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            
            print(f"{day} {start_str}:{end_str}")
            return
    
    # If no solution found, but task says there exists one, so this should not happen
    print("No suitable time found")

def compute_free_intervals(busy_intervals, work_start, work_end):
    # Sort busy intervals by start time
    busy_intervals.sort(key=lambda x: x[0])
    free_intervals = []
    current = work_start
    
    for start, end in busy_intervals:
        if current < start:
            free_intervals.append((current, start))
        current = max(current, end)
    
    if current < work_end:
        free_intervals.append((current, work_end))
    
    return free_intervals

def find_common_free_intervals(intervals1, intervals2):
    common = []
    i = j = 0
    while i < len(intervals1) and j < len(intervals2):
        a1, b1 = intervals1[i]
        a2, b2 = intervals2[j]
        
        # Find overlap
        start = max(a1, a2)
        end = min(b1, b2)
        if start < end:
            common.append((start, end))
        
        # Move to next interval
        if b1 < b2:
            i += 1
        else:
            j += 1
    
    return common

if __name__ == "__main__":
    main()