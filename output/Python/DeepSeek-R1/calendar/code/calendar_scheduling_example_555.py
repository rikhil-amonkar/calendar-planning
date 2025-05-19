def find_meeting_time():
    # Work hours and constraints
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30
    day = "Monday"
    
    # Evelyn's availability (before 13:00)
    evelyn_available = [(9*60, 13*60)]
    
    # Randy's blocked times converted to free slots within work hours
    randy_blocked = [(9*60, 10.5*60), (11*60, 15.5*60), (16*60, 17*60)]
    randy_free = []
    previous_end = work_start
    for start, end in sorted(randy_blocked):
        if start > previous_end:
            randy_free.append((previous_end, start))
        previous_end = end
    if previous_end < work_end:
        randy_free.append((previous_end, work_end))
    
    # Find overlapping slots that satisfy Evelyn's time preference
    for e_start, e_end in evelyn_available:
        for r_start, r_end in randy_free:
            overlap_start = max(e_start, r_start)
            overlap_end = min(e_end, r_end)
            if overlap_end - overlap_start >= meeting_duration:
                # Convert minutes back to HH:MM format
                return (
                    f"{day}: "
                    f"{int(overlap_start//60):02d}:{int(overlap_start%60):02d}:"
                    f"{int((overlap_start+meeting_duration)//60):02d}:{int((overlap_start+meeting_duration)%60):02d}"
                )
    
    return "No suitable time found"

print(find_meeting_time())