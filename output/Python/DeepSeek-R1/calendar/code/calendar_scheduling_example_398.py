def find_meeting_time():
    # Define work hours
    work_start = 9 * 60
    work_end = 17 * 60
    duration = 30

    # Convert blocked times to minutes since midnight
    blocked = {
        'Doris': [(9*60, 11*60), (13*60+30, 14*60), (16*60, 16*60+30)],
        'Theresa': [(10*60, 12*60)],
        'Christian': [],
        'Terry': [(9*60+30, 10*60), (11*60+30, 12*60), (12*60+30, 13*60),
                  (13*60+30, 14*60), (14*60+30, 15*60), (15*60+30, 17*60)],
        'Carolyn': [(9*60, 10*60+30), (11*60, 11*60+30), (12*60, 13*60),
                    (13*60+30, 14*60+30), (15*60, 17*60)],
        'Kyle': [(9*60, 9*60+30), (11*60+30, 12*60), (12*60+30, 13*60),
                 (14*60+30, 17*60)]
    }

    # Check every minute in work hours
    for start in range(work_start, work_end - duration + 1):
        end = start + duration
        conflict = False
        # Check all participants' schedules
        for person, blocks in blocked.items():
            for block_start, block_end in blocks:
                if not (end <= block_start or start >= block_end):
                    conflict = True
                    break
            if conflict:
                break
        if not conflict:
            # Format time as HH:MM:HH:MM
            s_h, s_m = divmod(start, 60)
            e_h, e_m = divmod(end, 60)
            return f"Monday {s_h:02}:{s_m:02}:{e_h:02}:{e_m:02}"
    
    return "No available time found"

print(find_meeting_time())