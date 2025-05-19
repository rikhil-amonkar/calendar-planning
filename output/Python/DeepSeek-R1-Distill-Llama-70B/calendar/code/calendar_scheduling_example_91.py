def find_meeting_time():
    # Define the schedules for each participant
    schedules = {
        "Danielle": [(9, 0, 10, 0), (10, 30, 11, 0), (14, 30, 15, 0), (15, 30, 16, 0), (16, 30, 17, 0)],
        "Bruce": [(11, 0, 11, 30), (12, 30, 13, 0), (14, 0, 14, 30), (15, 30, 16, 0)],
        "Eric": [(9, 0, 9, 30), (10, 0, 11, 0), (11, 30, 13, 0), (14, 30, 15, 30)]
    }

    # Convert time ranges to minutes since midnight for easier calculations
    def time_to_minutes(hours, minutes):
        return hours * 60 + minutes

    # Check each possible time slot
    start_time = 9 * 60  # 9:00 in minutes
    end_time = 17 * 60   # 17:00 in minutes

    # Iterate through each hour-long slot
    while start_time < end_time:
        current_end = start_time + 60
        if current_end > end_time:
            current_end = end_time

        # Convert start and end times back to HH:MM format
        start_hh, start_mm = divmod(start_time, 60)
        end_hh, end_mm = divmod(current_end, 60)

        # Check if this time slot works for everyone
        works_for_all = True
        for name, schedule in schedules.items():
            for meeting in schedule:
                meeting_start = time_to_minutes(meeting[0], meeting[1])
                meeting_end = time_to_minutes(meeting[2], meeting[3])
                
                # Check overlap
                if not (current_end <= meeting_start or start_time >= meeting_end):
                    works_for_all = False
                    break
            if not works_for_all:
                break

        if works_for_all:
            return f"Monday: {start_hh:02d}:{start_mm:02d}-{end_hh:02d}:{end_mm:02d}"
        
        start_time += 60  # Move to the next hour-long slot

    # If no time found (should not happen as per problem statement)
    return "No available time found"

# Execute the function
print(find_meeting_time())