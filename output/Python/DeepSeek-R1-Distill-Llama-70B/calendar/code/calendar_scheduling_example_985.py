def find_meeting_time():
    # Define the schedules for each participant
    diane_schedule = {
        "Monday": [(12, 0, 12, 30), (15, 0, 15, 30)],
        "Tuesday": [(10, 0, 11, 0), (11, 30, 12, 0), (12, 30, 13, 0), (16, 0, 17, 0)],
        "Wednesday": [(9, 0, 9, 30), (14, 30, 15, 0), (16, 30, 17, 0)],
        "Thursday": [(15, 30, 16, 30)],
        "Friday": [(9, 30, 11, 30), (14, 30, 15, 0), (16, 0, 17, 0)]
    }

    matthew_schedule = {
        "Monday": [(9, 0, 10, 0), (10, 30, 17, 0)],
        "Tuesday": [(9, 0, 17, 0)],
        "Wednesday": [(9, 0, 11, 0), (12, 0, 14, 30), (16, 0, 17, 0)],
        "Thursday": [(9, 0, 16, 0)],
        "Friday": [(9, 0, 17, 0)]
    }

    # Define the meeting duration in hours
    meeting_duration = 1

    # Define the work hours
    work_hours = (9, 0, 17, 0)

    # Iterate through each day
    for day in ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]:
        # Check if Matthew has a preference for this day
        if day == "Wednesday":
            matthew_preferred_start = (12, 30)
        else:
            matthew_preferred_start = None

        # Get the busy intervals for both participants
        diane_busy = diane_schedule[day]
        matthew_busy = matthew_schedule[day]

        # Combine and sort all busy intervals for the day
        all_busy = sorted(diane_busy + matthew_busy, key=lambda x: (x[0], x[1]))

        # Generate possible time slots
        possible_slots = []
        current_start = list(work_hours[:2])

        for interval in all_busy:
            start_hour, start_minute, end_hour, end_minute = interval
            if (current_start[0], current_start[1]) < (start_hour, start_minute):
                possible_slots.append((current_start[0], current_start[1], start_hour, start_minute))
            current_start = [end_hour, end_minute]

        # Add the slot after the last busy interval
        if current_start[0] < work_hours[2]:
            possible_slots.append((current_start[0], current_start[1], work_hours[2], work_hours[3]))

        # Check each possible slot for availability
        for slot in possible_slots:
            slot_start = (slot[0], slot[1])
            slot_end = (slot[2], slot[3])

            # Check if the slot fits the meeting duration
            if (slot_end[0] - slot_start[0]) >= meeting_duration or \
               (slot_end[0] == slot_start[0] and slot_end[1] - slot_start[1] >= meeting_duration * 60):
                # Check Matthew's preference
                if matthew_preferred_start and (slot_start[0] < matthew_preferred_start[0] or 
                                               (slot_start[0] == matthew_preferred_start[0] and slot_start[1] < matthew_preferred_start[1])):
                    continue

                # Convert slot to required format and return
                return f"{slot[0]:02d}:{slot[1]:02d}:{slot[2]:02d}:{slot[3]:02d}", day

    # If no slot found (should not happen as per problem statement)
    return None

# Execute the function
meeting_time, day = find_meeting_time()
print(f"Meeting scheduled for {day} at {meeting_time}")