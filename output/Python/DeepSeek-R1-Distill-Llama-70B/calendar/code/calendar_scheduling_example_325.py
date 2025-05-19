def find_meeting_time():
    # Define the schedules for each participant
    schedules = {
        "Jose": [(11, 0, 11, 30), (12, 30, 13, 0)],
        "Keith": [(14, 0, 14, 30), (15, 0, 15, 30)],
        "Logan": [(9, 0, 10, 0), (12, 0, 12, 30), (15, 0, 15, 30)],
        "Megan": [(9, 0, 10, 30), (11, 0, 12, 0), (13, 0, 13, 30), (14, 30, 16, 30)],
        "Gary": [(9, 0, 9, 30), (10, 0, 10, 30), (11, 30, 13, 0), (13, 30, 14, 0), (14, 30, 16, 30)],
        "Bobby": [(11, 0, 11, 30), (12, 0, 12, 30), (13, 0, 16, 0)]
    }

    # Convert time ranges to minutes since midnight for easier calculations
    def time_to_minutes(hours, minutes):
        return hours * 60 + minutes

    # Check each possible time slot
    start_time = 9 * 60  # 9:00 in minutes
    end_time = 17 * 60   # 17:00 in minutes

    # Iterate through each 30-minute slot
    while start_time < end_time:
        current_end = start_time + 30
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
        
        start_time += 30  # Move to the next 30-minute slot

    # If no time found (should not happen as per problem statement)
    return "No available time found"

# Execute the function
print(find_meeting_time())