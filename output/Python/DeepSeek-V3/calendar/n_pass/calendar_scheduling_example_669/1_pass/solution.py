def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday']
    meeting_duration = 30  # minutes

    # Define busy slots for each participant per day in minutes since midnight
    jean_busy = {
        'Monday': [],
        'Tuesday': [(11 * 60 + 30, 12 * 60), (16 * 60, 16 * 60 + 30)]
    }

    doris_busy = {
        'Monday': [
            (9 * 60, 11 * 60 + 30),
            (12 * 60, 12 * 60 + 30),
            (13 * 60 + 30, 16 * 60),
            (16 * 60 + 30, 17 * 60)
        ],
        'Tuesday': [(9 * 60, 17 * 60)]  # Entire day is busy
    }

    doris_preference = {
        'Monday': (14 * 60, 17 * 60)  # Prefers not to meet after 14:00
    }

    # Iterate through each day to find a suitable time
    for day in days:
        # Collect all busy slots for both participants on this day
        busy_slots = jean_busy[day] + doris_busy[day]
        busy_slots.sort()  # Sort by start time

        # Merge overlapping or adjacent busy slots
        merged_busy = []
        for start, end in busy_slots:
            if not merged_busy:
                merged_busy.append((start, end))
            else:
                last_start, last_end = merged_busy[-1]
                if start <= last_end:
                    # Overlapping or adjacent, merge them
                    new_start = min(last_start, start)
                    new_end = max(last_end, end)
                    merged_busy[-1] = (new_start, new_end)
                else:
                    merged_busy.append((start, end))

        # Find free slots by checking gaps between busy slots
        free_slots = []
        prev_end = work_start
        for start, end in merged_busy:
            if start > prev_end:
                free_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        if prev_end < work_end:
            free_slots.append((prev_end, work_end))

        # Check each free slot for availability and duration
        for start, end in free_slots:
            slot_duration = end - start
            if slot_duration >= meeting_duration:
                # Check Doris's preference for Monday after 14:00
                if day == 'Monday' and start >= doris_preference['Monday'][0]:
                    continue  # Skip if it's after 14:00 on Monday
                # Found a suitable slot
                meeting_start = start
                meeting_end = meeting_start + meeting_duration
                # Convert minutes back to HH:MM format
                def format_time(minutes):
                    hh = minutes // 60
                    mm = minutes % 60
                    return f"{hh:02d}:{mm:02d}"
                time_range = f"{format_time(meeting_start)}:{format_time(meeting_end)}"
                return day, time_range

    return None, None  # No suitable time found (though problem states there is one)

day, time_range = find_meeting_time()
print(f"{day}: {time_range}")