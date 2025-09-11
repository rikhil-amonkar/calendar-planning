def get_free_intervals(busy_intervals, work_start=540, work_end=1020):
    # Sort busy intervals by start time
    busy_intervals = sorted(busy_intervals, key=lambda x: x[0])
    free = [(work_start, work_end)]
    for b_start, b_end in busy_intervals:
        new_free = []
        for f_start, f_end in free:
            if b_end <= f_start:
                new_free.append((f_start, f_end))
            elif b_start >= f_end:
                new_free.append((f_start, f_end))
            else:
                # Split into parts before and after the busy interval
                if f_start < b_start:
                    new_free.append((f_start, b_start))
                if f_end > b_end:
                    new_free.append((b_end, f_end))
        free = new_free
    return free

def find_meeting_time():
    # Define busy intervals for each person and day
    nicole_busy = {
        'Monday': [(540, 570), (780, 810), (870, 930)],
        'Tuesday': [(540, 570), (690, 810), (870, 930)],
        'Wednesday': [(600, 660), (750, 900), (960, 1020)]
    }
    ruth_busy = {
        'Monday': [(540, 1020)],
        'Tuesday': [(540, 1020)],
        'Wednesday': [(540, 630), (660, 690), (720, 750), (810, 1020)]
    }
    
    days = ['Monday', 'Tuesday', 'Wednesday']
    for day in days:
        # Get free intervals for Nicole and Ruth
        nicole_free = get_free_intervals(nicole_busy.get(day, []))
        ruth_free = get_free_intervals(ruth_busy.get(day, []))
        
        # Find overlapping intervals
        overlapping = []
        for n_start, n_end in nicole_free:
            for r_start, r_end in ruth_free:
                overlap_start = max(n_start, r_start)
                overlap_end = min(n_end, r_end)
                if overlap_start < overlap_end:
                    overlapping.append((overlap_start, overlap_end))
        
        # Check if any overlapping interval can fit 30 minutes
        for start, end in overlapping:
            duration = end - start
            if duration >= 30:
                # Return the earliest possible (start to start+30)
                meeting_start = start
                meeting_end = start + 30
                # Convert to HH:MM format
                day_of_week = day
                # Output the time and day
                start_time = f"{meeting_start//60:02d}:{meeting_start%60:02d}"
                end_time = f"{meeting_end//60:02d}:{meeting_end%60:02d}"
                print(f"{start_time}:{end_time} {day_of_week}")
                return
    
    # According to the problem, there is a solution, so this return is just for safety
    print("No solution found")

# Execute the function
find_meeting_time()