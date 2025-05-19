def find_meeting_time():
    # Define work hours and day
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    day = "Monday"
    duration = 60  # 1 hour
    
    # Convert schedules to minutes since midnight
    schedules = {
        "Julie": [(9*60, 9*60+30), (11*60, 11*60+30), (12*60, 12*60+30),
                  (13*60+30, 14*60), (16*60, 17*60)],
        "Sean": [(9*60, 9*60+30), (13*60, 13*60+30), (15*60, 15*60+30),
                 (16*60, 16*60+30)],
        "Lori": [(10*60, 10*60+30), (11*60, 13*60), (15*60+30, 17*60)]
    }
    
    # Create a merged busy timeline
    timeline = [0] * (work_end - work_start)
    for person, busy_slots in schedules.items():
        for start, end in busy_slots:
            for t in range(max(start, work_start) - work_start, 
                          min(end, work_end) - work_start):
                timeline[t] += 1
    
    # Find first available slot
    current_start = None
    for i, count in enumerate(timeline):
        if count == 0:
            if current_start is None:
                current_start = i
            if i - current_start + 1 >= duration:
                # Convert back to time
                start_h = (work_start + current_start) // 60
                start_m = (work_start + current_start) % 60
                end_h = (work_start + current_start + duration) // 60
                end_m = (work_start + current_start + duration) % 60
                return (
                    f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}",
                    day
                )
        else:
            current_start = None
    
    return None

time_range, day = find_meeting_time()
print(f"{day}:{time_range}")