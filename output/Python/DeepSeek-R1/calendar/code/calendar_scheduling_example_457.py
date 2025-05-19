def find_meeting_time():
    # Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
    work_start = 540
    work_end = 1020
    duration = 30

    # Convert all schedules to minutes since midnight for easier comparison
    schedules = {
        'Andrea': [(570, 630), (810, 870)],
        'Ruth': [(750, 780), (900, 930)],
        'Steven': [(600, 630), (660, 690), (720, 750), (810, 840), (900, 960)],
        'Grace': [],
        'Kyle': [(540, 570), (630, 720), (750, 780), (810, 900), (930, 960), (990, 1020)],
        'Elijah': [(540, 660), (690, 780), (810, 840), (930, 960), (990, 1020)],
        'Lori': [(540, 570), (600, 690), (720, 810), (840, 960), (990, 1020)]
    }

    # Check every minute in work hours for availability
    for start in range(work_start, work_end - duration + 1):
        end = start + duration
        conflict = False
        for person, busy in schedules.items():
            for busy_start, busy_end in busy:
                if not (end <= busy_start or start >= busy_end):
                    conflict = True
                    break
            if conflict:
                break
        if not conflict:
            # Convert back to HH:MM format
            def format_time(minutes):
                return f"{minutes // 60:02d}:{minutes % 60:02d}"
            
            return f"Monday {format_time(start)}-{format_time(end)}"
    
    return "No suitable time found"

meeting_time = find_meeting_time()
print(meeting_time)