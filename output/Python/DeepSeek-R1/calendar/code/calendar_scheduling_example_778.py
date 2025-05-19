def find_meeting_time():
    import datetime

    def time_to_minutes(t):
        return t.hour * 60 + t.minute

    def minutes_to_time(m):
        hours = m // 60
        minutes = m % 60
        return datetime.time(hours, minutes)

    days = ['Monday', 'Wednesday', 'Tuesday']
    work_start = datetime.time(9, 0)
    work_end = datetime.time(17, 0)
    duration = 30

    # Define schedules for each day
    schedules = {
        'Monday': {
            'Susan': [(datetime.time(12, 30), datetime.time(13, 0)),
                      (datetime.time(13, 30), datetime.time(14, 0))],
            'Sandra': [(datetime.time(9, 0), datetime.time(13, 0)),
                       (datetime.time(14, 0), datetime.time(15, 0)),
                       (datetime.time(16, 0), datetime.time(16, 30))]
        },
        'Wednesday': {
            'Susan': [(datetime.time(9, 30), datetime.time(10, 30)),
                      (datetime.time(14, 0), datetime.time(14, 30)),
                      (datetime.time(15, 30), datetime.time(16, 30))],
            'Sandra': [(datetime.time(9, 0), datetime.time(11, 30)),
                       (datetime.time(12, 0), datetime.time(12, 30)),
                       (datetime.time(13, 0), datetime.time(17, 0))]
        },
        'Tuesday': {
            'Susan': [(datetime.time(11, 30), datetime.time(12, 0))],
            'Sandra': [(datetime.time(9, 0), datetime.time(9, 30)),
                       (datetime.time(10, 30), datetime.time(12, 0)),
                       (datetime.time(12, 30), datetime.time(13, 30)),
                       (datetime.time(14, 0), datetime.time(14, 30)),
                       (datetime.time(16, 0), datetime.time(17, 0))]
        }
    }

    for day in days:
        if day == 'Tuesday':  # Susan's preference
            continue
        
        susan_busy = schedules[day]['Susan']
        sandra_busy = schedules[day]['Sandra']

        # Convert busy times to minutes
        def convert_intervals(intervals):
            converted = []
            for start, end in intervals:
                s = time_to_minutes(start)
                e = time_to_minutes(end)
                converted.append((s, e))
            return converted
        
        susan_blocked = convert_intervals(susan_busy)
        sandra_blocked = convert_intervals(sandra_busy)

        # Generate free slots
        def get_free_slots(blocked, work_start, work_end):
            start_min = time_to_minutes(work_start)
            end_min = time_to_minutes(work_end)
            blocked = sorted(blocked + [(end_min, end_min)])
            free = []
            prev_end = start_min
            for s, e in blocked:
                if s > prev_end:
                    free.append((prev_end, s))
                prev_end = max(prev_end, e)
            return free
        
        susan_free = get_free_slots(susan_blocked, work_start, work_end)
        sandra_free = get_free_slots(sandra_blocked, work_start, work_end)

        # Apply Sandra's Monday constraint
        if day == 'Monday':
            sandra_free = [ (s, e) for (s, e) in sandra_free if e <= 960 ]  # 16:00 in minutes

        # Find overlapping slots
        combined_free = []
        i = j = 0
        while i < len(susan_free) and j < len(sandra_free):
            s_start, s_end = susan_free[i]
            sa_start, sa_end = sandra_free[j]

            start = max(s_start, sa_start)
            end = min(s_end, sa_end)
            if start < end:
                combined_free.append((start, end))
            if s_end < sa_end:
                i += 1
            else:
                j += 1

        # Check for valid slot
        for start, end in combined_free:
            if end - start >= duration:
                meeting_start = start
                meeting_end = meeting_start + duration
                start_time = minutes_to_time(meeting_start)
                end_time = minutes_to_time(meeting_end)
                return (day, f"{start_time.hour:02d}:{start_time.minute:02d}:{end_time.hour:02d}:{end_time.minute:02d}")

    # Fallback to Tuesday if necessary (though problem states solution exists)
    day = 'Tuesday'
    susan_busy = schedules[day]['Susan']
    sandra_busy = schedules[day]['Sandra']
    susan_blocked = convert_intervals(susan_busy)
    sandra_blocked = convert_intervals(sandra_busy)
    susan_free = get_free_slots(susan_blocked, work_start, work_end)
    sandra_free = get_free_slots(sandra_blocked, work_start, work_end)
    combined_free = []
    i = j = 0
    while i < len(susan_free) and j < len(sandra_free):
        s_start, s_end = susan_free[i]
        sa_start, sa_end = sandra_free[j]
        start = max(s_start, sa_start)
        end = min(s_end, sa_end)
        if start < end:
            combined_free.append((start, end))
        if s_end < sa_end:
            i += 1
        else:
            j += 1
    for start, end in combined_free:
        if end - start >= duration:
            meeting_start = start
            meeting_end = meeting_start + duration
            start_time = minutes_to_time(meeting_start)
            end_time = minutes_to_time(meeting_end)
            return (day, f"{start_time.hour:02d}:{start_time.minute:02d}:{end_time.hour:02d}:{end_time.minute:02d}")

day, time = find_meeting_time()
print(f"{day}:{time}")