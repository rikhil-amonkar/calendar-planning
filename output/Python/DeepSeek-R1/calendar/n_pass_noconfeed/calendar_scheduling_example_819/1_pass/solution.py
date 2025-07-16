from datetime import time

def main():
    # Define work hours
    work_start = time(9, 0)
    work_end = time(17, 0)
    
    # Define Ruth's busy times for each day
    busy_times = {
        'Monday': [(time(9, 0), time(17, 0))],
        'Tuesday': [(time(9, 0), time(17, 0))],
        'Wednesday': [(time(9, 0), time(17, 0))],
        'Thursday': [
            (time(9, 0), time(11, 0)),
            (time(11, 30), time(14, 30)),
            (time(15, 0), time(17, 0))
        ]
    }
    
    candidate_day = None
    candidate_start = None
    candidate_end = None
    
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    
    for day in days:
        busy_intervals = busy_times[day]
        # Sort busy intervals by start time
        busy_intervals_sorted = sorted(busy_intervals, key=lambda x: x[0])
        free_intervals = []
        current = work_start
        
        # Compute free intervals by subtracting busy times
        for busy_start, busy_end in busy_intervals_sorted:
            if current < busy_start:
                free_intervals.append((current, busy_start))
            current = max(current, busy_end)
        if current < work_end:
            free_intervals.append((current, work_end))
        
        # Check each free interval for availability
        for start, end in free_intervals:
            start_minutes = start.hour * 60 + start.minute
            end_minutes = end.hour * 60 + end.minute
            duration = end_minutes - start_minutes
            if duration < 30:  # Skip if less than meeting duration
                continue
            
            # Calculate slot end time
            slot_end_minutes = start_minutes + 30
            slot_end_hr = slot_end_minutes // 60
            slot_end_min = slot_end_minutes % 60
            slot_end = time(slot_end_hr, slot_end_min)
            
            # Apply Julie's preference: avoid Thursday before 11:30
            if day == 'Thursday' and start < time(11, 30):
                continue  # Skip this slot
            
            candidate_day = day
            candidate_start = start
            candidate_end = slot_end
            break  # Found a candidate, break inner loop
        
        if candidate_day:
            break  # Found a candidate, break outer loop
    
    # Format the output
    if candidate_day:
        start_str = candidate_start.strftime('%H:%M')
        end_str = candidate_end.strftime('%H:%M')
        time_range = f"{start_str}:{end_str}"
        print(candidate_day)
        print(time_range)
    else:
        print("No suitable time found")  # Should not happen per problem statement

if __name__ == "__main__":
    main()