def find_meeting_time(eugene_schedule, eric_schedule, eric_preferred_days):
    # Validate the schedules
    for day in ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']:
        if day not in eugene_schedule or day not in eric_schedule:
            raise ValueError(f"Schedule for {day} is missing")

    # Sort the time blocks by start time
    for day in ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']:
        eugene_schedule[day].sort(key=lambda x: x[0])
        eric_schedule[day].sort(key=lambda x: x[0])

    # Find the first non-conflicting time block
    meeting_start = None
    for day in ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']:
        eugene_time_blocks = eugene_schedule[day]
        eric_time_blocks = eric_schedule[day]

        # Find the first non-conflicting time block
        eugene_index = 0
        eric_index = 0
        while eugene_index < len(eugene_time_blocks) and eric_index < len(eric_time_blocks):
            eugene_start, eugene_end = eugene_time_blocks[eugene_index]
            eric_start, eric_end = eric_time_blocks[eric_index]

            # Check if the time blocks conflict
            if eugene_start < eric_end and eric_start < eugene_end:
                # Move to the next time block
                eugene_index += 1
                eric_index += 1
            else:
                # Find the meeting start time
                if eugene_start < eric_start:
                    meeting_start = eugene_start
                else:
                    meeting_start = eric_start

                # Find the meeting end time
                if eugene_end > eric_end:
                    meeting_start = eric_end
                else:
                    meeting_start = eugene_end

                # Return the meeting start time
                return meeting_start, meeting_start + 0.5

        # If no meeting time is found, move to the next day
        if day == 'Friday':
            break

    # If no meeting time is found, return None
    return None

# Define the schedules for Eugene and Eric
eugene_schedule = {
    'Monday': [(9, 9.5), (11, 11.5), (12, 12.5), (13, 15)],
    'Tuesday': [],
    'Wednesday': [(9, 9.5), (12, 14), (14, 16.5)],
    'Thursday': [(9, 10), (11, 12.5)],
    'Friday': [(10, 10.5), (12, 12.5), (13, 13.5)]
}

eric_schedule = {
    'Monday': [(9, 17)],
    'Tuesday': [(9, 17)],
    'Wednesday': [(9, 11.5), (12, 14), (14, 16.5)],
    'Thursday': [(9, 17)],
    'Friday': [(9, 11.5), (12, 14), (14, 16.5)]
}

# Find the meeting time
meeting_start, meeting_end = find_meeting_time(eugene_schedule, eric_schedule, ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday'])

# Print the meeting time
if meeting_start is not None:
    print(f"Meeting time: {meeting_start} - {meeting_end}")
else:
    print("No meeting time found")