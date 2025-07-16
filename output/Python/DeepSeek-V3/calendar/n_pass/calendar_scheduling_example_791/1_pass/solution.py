def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    meeting_duration = 30  # minutes

    # Define busy times for each person in minutes since midnight
    nicole_busy = {
        'Monday': [(9*60, 9*60 + 30), (13*60, 13*60 + 30), (14*60 + 30, 15*60 + 30)],
        'Tuesday': [(9*60, 9*60 + 30), (11*60 + 30, 13*60 + 30), (14*60 + 30, 15*60 + 30)],
        'Wednesday': [(10*60, 11*60), (12*60 + 30, 15*60), (16*60, 17*60)]
    }

    ruth_busy = {
        'Monday': [(9*60, 17*60)],
        'Tuesday': [(9*60, 17*60)],
        'Wednesday': [(9*60, 10*60 + 30), (11*60, 11*60 + 30), (12*60, 12*60 + 30), (13*60 + 30, 15*60 + 30), (16*60, 16*60 + 30)]
    }

    # Ruth's preference: not after 13:30 on Wednesday
    ruth_preference = {
        'Wednesday': (13*60 + 30)
    }

    # Iterate through each day to find a suitable time
    for day in days:
        if day == 'Wednesday' and day in ruth_preference:
            # Adjust work_end for Wednesday based on Ruth's preference
            current_work_end = min(work_end, ruth_preference[day])
        else:
            current_work_end = work_end

        # Generate all possible time slots for the day
        possible_slots = []
        current_time = work_start
        while current_time + meeting_duration <= current_work_end:
            possible_slots.append((current_time, current_time + meeting_duration))
            current_time += meeting_duration

        # Check each slot against Nicole's and Ruth's busy times
        for slot_start, slot_end in possible_slots:
            # Check Nicole's availability
            nicole_available = True
            for busy_start, busy_end in nicole_busy.get(day, []):
                if not (slot_end <= busy_start or slot_start >= busy_end):
                    nicole_available = False
                    break

            # Check Ruth's availability
            ruth_available = True
            for busy_start, busy_end in ruth_busy.get(day, []):
                if not (slot_end <= busy_start or slot_start >= busy_end):
                    ruth_available = False
                    break

            if nicole_available and ruth_available:
                # Format the time as HH:MM:HH:MM
                start_hh = slot_start // 60
                start_mm = slot_start % 60
                end_hh = slot_end // 60
                end_mm = slot_end % 60
                time_str = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
                return day, time_str

    return None, None

day, time_slot = find_meeting_time()
if day and time_slot:
    print(f"{day}: {time_slot}")
else:
    print("No suitable time found.")