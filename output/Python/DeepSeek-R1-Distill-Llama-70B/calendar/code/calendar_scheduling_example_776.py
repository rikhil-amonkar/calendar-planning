def find_meeting_time():
    # Define the schedules for each participant
    jennifer_schedule = {
        "Monday": [(9, 0, 11, 0), (11, 30, 13, 0), (13, 30, 14, 30), (15, 0, 17, 0)],
        "Tuesday": [(9, 0, 11, 30), (12, 0, 17, 0)],
        "Wednesday": [(9, 0, 11, 30), (12, 0, 12, 30), (13, 0, 14, 0), (14, 30, 16, 0), (16, 30, 17, 0)]
    }

    # Convert time ranges to minutes since midnight for easier calculations
    def time_to_minutes(hours, minutes):
        return hours * 60 + minutes

    # Check each day in order of preference
    for day in ["Monday", "Tuesday", "Wednesday"]:
        schedule = jennifer_schedule[day]
        # Sort the schedule by start time
        schedule.sort(key=lambda x: (x[0], x[1]))
        
        # Check for available slots before the first meeting
        if schedule[0][0] > 9:
            start_time = (9, 0)
            end_time = (9, 30)
            if time_to_minutes(end_time[0], end_time[1]) <= time_to_minutes(schedule[0][0], schedule[0][1]):
                return f"{day}: {start_time[0]:02d}:{start_time[1]:02d}-{end_time[0]:02d}:{end_time[1]:02d}"
        
        # Check for gaps between meetings
        for i in range(len(schedule) - 1):
            current_end = schedule[i][2], schedule[i][3]
            next_start = schedule[i+1][0], schedule[i+1][1]
            
            gap_start = current_end
            gap_end = next_start
            
            if gap_end[0] == gap_start[0] and gap_end[1] == gap_start[1]:
                continue  # No gap
            
            # Calculate the duration of the gap
            gap_duration = (gap_end[0] - gap_start[0]) * 60 + (gap_end[1] - gap_start[1])
            
            if gap_duration >= 30:
                # Check if the gap is within working hours
                if gap_start[0] >= 9 and gap_end[0] <= 17:
                    # Check John's preference for Monday
                    if day == "Monday" and gap_start[0] >= 14:  # After 14:30
                        continue  # Skip this gap
                    return f"{day}: {gap_start[0]:02d}:{gap_start[1]:02d}-{gap_start[0]:02d}:{gap_start[1]+30:02d}"
        
        # Check for available slots after the last meeting
        last_end = schedule[-1][2], schedule[-1][3]
        if last_end[0] < 17:
            start_time = last_end
            end_time = (start_time[0], start_time[1] + 30)
            if end_time[0] > 17:
                end_time = (17, 0)
            if end_time[0] == start_time[0] and end_time[1] < start_time[1]:
                continue  # Not enough time
            if day == "Monday" and start_time[0] >= 14:  # After 14:30
                continue  # Skip this slot
            return f"{day}: {start_time[0]:02d}:{start_time[1]:02d}-{end_time[0]:02d}:{end_time[1]:02d}"

    # Default case (should not happen as per problem statement)
    return "No available time found"

# Execute the function
print(find_meeting_time())