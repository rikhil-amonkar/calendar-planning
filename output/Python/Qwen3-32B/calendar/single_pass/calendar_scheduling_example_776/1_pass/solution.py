def find_meeting_time():
    busy_times = {
        'Monday': [
            (9.0, 11.0),
            (11.5, 13.0),
            (13.5, 14.5),
            (15.0, 17.0)
        ],
        'Tuesday': [
            (9.0, 11.5),
            (12.0, 17.0)
        ],
        'Wednesday': [
            (9.0, 11.5),
            (12.0, 12.5),
            (13.0, 14.0),
            (14.5, 16.0),
            (16.5, 17.0)
        ]
    }

    days = ['Monday', 'Tuesday', 'Wednesday']
    for day in days:
        busy = busy_times[day]
        free_slots = []
        prev_end = 9.0
        for start, end in busy:
            if prev_end < start:
                free_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        if prev_end < 17.0:
            free_slots.append((prev_end, 17.0))
        for slot in free_slots:
            duration = slot[1] - slot[0]
            if duration >= 0.5:
                start_time = slot[0]
                end_time = start_time + 0.5
                # Check John's constraint for Monday
                if day == 'Monday' and start_time >= 14.5:
                    continue
                # Convert to HH:MM
                def to_time_str(h):
                    hours = int(h)
                    minutes = int((h * 60)) % 60
                    return f"{hours:02d}:{minutes:02d}"
                start_str = to_time_str(start_time)
                end_str = to_time_str(end_time)
                print(f"{day} {start_str}:{end_str}")
                return

find_meeting_time()