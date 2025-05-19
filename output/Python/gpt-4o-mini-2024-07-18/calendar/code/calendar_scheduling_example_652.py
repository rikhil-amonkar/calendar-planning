# Define the existing schedules
jesse_schedule = {
    "Monday": [(9, 17)],
    "Tuesday": [(9, 9.5), (13, 13.5), (14, 15)]
}

lawrence_schedule = {
    "Monday": [(9, 17)],
    "Tuesday": [(9.5, 10.5), (11.5, 12.5), (13, 13.5), (14.5, 15), (15.5, 16.5)]
}

# Meeting duration in hours
meeting_duration = 0.5

# Function to find available time
def find_meeting_time(jesse_schedule, lawrence_schedule, meeting_duration):
    for day in ["Monday", "Tuesday"]:
        jesse_busy_times = jesse_schedule[day]
        lawrence_busy_times = lawrence_schedule[day]

        # Create a list of all busy times
        busy_times = jesse_busy_times + lawrence_busy_times
        
        # Include work hours
        if day == "Monday":
            busy_times.append((9, 17))
        elif day == "Tuesday":
            busy_times.append((9, 16.5))

        # Sort and merge busy times
        busy_times.sort()
        merged_busy_times = []
        for start, end in busy_times:
            if not merged_busy_times or merged_busy_times[-1][1] < start:
                merged_busy_times.append((start, end))
            else:
                merged_busy_times[-1] = (merged_busy_times[-1][0], max(merged_busy_times[-1][1], end))
        
        # Find gaps in the merged busy times
        last_end = 9  # Work hours start at 9
        for start, end in merged_busy_times:
            if last_end + meeting_duration <= start:
                return f"{day} {last_end:.2f} {last_end + meeting_duration:.2f}"
            last_end = end
        
        # Check after the last booked time until the end of the workday
        if last_end + meeting_duration <= (17 if day == "Monday" else 16.5):
            return f"{day} {last_end:.2f} {last_end + meeting_duration:.2f}"

# Call the function and print the result
meeting_time = find_meeting_time(jesse_schedule, lawrence_schedule, meeting_duration)
print(meeting_time)