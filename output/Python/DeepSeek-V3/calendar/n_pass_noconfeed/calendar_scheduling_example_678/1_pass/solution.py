def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes

    # Define days to consider
    days = ['Monday', 'Tuesday']

    # Define busy times for each person in minutes since midnight
    # Format: (start, end)
    russell_busy = {
        'Monday': [(10 * 60 + 30, 11 * 60)],  # 10:30-11:00
        'Tuesday': [(13 * 60, 13 * 60 + 30)]  # 13:00-13:30
    }

    alexander_busy = {
        'Monday': [
            (9 * 60, 11 * 60 + 30),  # 9:00-11:30
            (12 * 60, 14 * 60 + 30),  # 12:00-14:30
            (15 * 60, 17 * 60)        # 15:00-17:00
        ],
        'Tuesday': [
            (9 * 60, 10 * 60),        # 9:00-10:00
            (13 * 60, 14 * 60),        # 13:00-14:00
            (15 * 60, 15 * 60 + 30),   # 15:00-15:30
            (16 * 60, 16 * 60 + 30)   # 16:00-16:30
        ]
    }

    # Russell's preference: not before 13:30 on Tuesday
    russell_preference = {
        'Tuesday': 13 * 60 + 30  # 13:30
    }

    # Iterate through each day
    for day in days:
        # Combine busy times for both participants
        busy_times = russell_busy.get(day, []) + alexander_busy.get(day, [])
        # Sort by start time
        busy_times.sort()

        # Initialize potential start time
        potential_start = work_start

        # Check Russell's preference for Tuesday
        if day == 'Tuesday':
            potential_start = max(potential_start, russell_preference['Tuesday'])

        # Merge overlapping or adjacent busy times
        merged_busy = []
        for start, end in busy_times:
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

        # Check for available slots
        for busy_start, busy_end in merged_busy:
            if potential_start + meeting_duration <= busy_start:
                # Found a slot
                meeting_end = potential_start + meeting_duration
                # Convert to HH:MM format
                start_hh = potential_start // 60
                start_mm = potential_start % 60
                end_hh = meeting_end // 60
                end_mm = meeting_end % 60
                return day, f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
            # Update potential_start to after this busy period
            potential_start = max(potential_start, busy_end)

        # Check after last busy period
        if potential_start + meeting_duration <= work_end:
            meeting_end = potential_start + meeting_duration
            start_hh = potential_start // 60
            start_mm = potential_start % 60
            end_hh = meeting_end // 60
            end_mm = meeting_end % 60
            return day, f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"

    return None, None

# Run the function and print the result
day, time_slot = find_meeting_time()
if day and time_slot:
    print(f"{day}: {time_slot}")
else:
    print("No suitable time found.")