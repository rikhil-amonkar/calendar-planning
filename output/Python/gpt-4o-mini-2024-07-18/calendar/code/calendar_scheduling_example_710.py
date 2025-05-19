from datetime import datetime, timedelta

# Define the participants' schedules
schedules = {
    "Cheryl": {
        "Monday": [(0, 9, 0, 9, 30), (0, 11, 30, 13, 0), (0, 15, 30, 16, 0)],
        "Tuesday": [(0, 15, 0, 15, 30)],
        "Wednesday": []
    },
    "Kyle": {
        "Monday": [(0, 9, 0, 17, 0)],
        "Tuesday": [(0, 9, 30, 17, 0)],
        "Wednesday": [(0, 9, 0, 9, 30), (0, 10, 0, 13, 0), (0, 13, 30, 14, 0), (0, 14, 30, 17, 0)]
    }
}

# Meeting duration in minutes
meeting_duration = 30

# Work hours
work_hours = {
    "Monday": (9, 17),
    "Tuesday": (9, 17),
    "Wednesday": (9, 17)
}

def find_available_time():
    for day in ["Monday", "Tuesday"]:
        # Get work hours
        start_hour, end_hour = work_hours[day]

        # Create a list of busy times
        busy_times = []
        for participant in schedules:
            busy_times.extend(schedules[participant][day])
        
        # Sort and merge busy times
        busy_times.sort()
        merged_busy_times = []
        
        for busy in busy_times:
            if merged_busy_times and merged_busy_times[-1][1] >= busy[1]:
                merged_busy_times[-1] = (merged_busy_times[-1][0], max(merged_busy_times[-1][1], busy[1]))
            else:
                merged_busy_times.append(busy)

        # Check for free time slots
        last_end = start_hour * 60  # Convert to minutes
        for busy in merged_busy_times:
            busy_start = busy[1] * 60  # Convert to minutes
            busy_end = busy[3] * 60    # Convert to minutes

            if busy_start - last_end >= meeting_duration:
                meeting_start = last_end
                meeting_end = meeting_start + meeting_duration
                if meeting_end <= busy_start:
                    return f"{day}: {meeting_start//60:02}:{meeting_start%60:02}:{meeting_end//60:02}:{meeting_end%60:02}"
            
            last_end = busy_end
        
        # Check after the last busy slot until the end of work hours
        if last_end < end_hour * 60 and (end_hour * 60) - last_end >= meeting_duration:
            meeting_start = last_end
            meeting_end = meeting_start + meeting_duration
            if meeting_end <= end_hour * 60:
                return f"{day}: {meeting_start//60:02}:{meeting_start%60:02}:{meeting_end//60:02}:{meeting_end%60:02}"

result = find_available_time()
print(result)