def find_meeting_time():
    # Define work hours and days
    work_hours = {'start': 9 * 60, 'end': 17 * 60}  # In minutes
    days = ['Monday', 'Tuesday']
    
    # Convert schedules to minutes since midnight
    russell_busy = {
        'Monday': [(10*60 + 30, 11*60)],
        'Tuesday': [(13*60, 13*60 + 30)]
    }
    
    alexander_busy = {
        'Monday': [(9*60, 11*60 + 30), (12*60, 14*60 + 30), (15*60, 17*60)],
        'Tuesday': [(9*60, 10*60), (13*60, 14*60), (15*60, 15*60 + 30), (16*60, 16*60 + 30)]
    }
    
    # Check each day
    for day in days:
        # Get free slots for both
        free_slots = []
        
        # Generate possible slots considering work hours and Russell's Tuesday preference
        for start in range(work_hours['start'], work_hours['end'] - 60 + 1, 15):
            end = start + 60
            if day == 'Tuesday' and end <= 13*60 + 30:  # Russell's Tuesday preference
                continue
            
            # Check Russell's availability
            russell_available = True
            for busy_start, busy_end in russell_busy.get(day, []):
                if not (end <= busy_start or start >= busy_end):
                    russell_available = False
                    break
            
            # Check Alexander's availability
            alexander_available = True
            for busy_start, busy_end in alexander_busy.get(day, []):
                if not (end <= busy_start or start >= busy_end):
                    alexander_available = False
                    break
            
            if russell_available and alexander_available:
                free_slots.append((start, end))
        
        # Find first suitable slot
        if free_slots:
            start, end = free_slots[0]
            return (f"{day}:{start//60:02}:{start%60:02}:{end//60:02}:{end%60:02}")
    
    return "No slot found"

result = find_meeting_time()
day, time_part = result.split(':')
start_h, start_m, end_h, end_m = map(int, time_part.split(':'))
print(f"{day}:{start_h:02}:{start_m:02}:{end_h:02}:{end_m:02}")