def find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes):
    # Convert work hours to minutes since midnight for easier calculation
    start_min = int(work_hours_start * 60)
    end_min = int(work_hours_end * 60)
    
    # Initialize a list to keep track of busy intervals for all participants
    busy_intervals = []
    
    for schedule in participants_schedules:
        for busy in schedule:
            # Convert all times to minutes, handling both float and int inputs
            start_busy = int(busy[0] * 60 + int(round((busy[0] % 1) * 60)))
            end_busy = int(busy[1] * 60 + int(round((busy[1] % 1) * 60)))
            busy_intervals.append((start_busy, end_busy))
    
    # Sort all busy intervals by start time
    busy_intervals.sort()
    
    # Merge overlapping or adjacent busy intervals
    merged = []
    for interval in busy_intervals:
        if not merged:
            merged.append(interval)
        else:
            last_start, last_end = merged[-1]
            current_start, current_end = interval
            if current_start <= last_end:
                # Overlapping or adjacent intervals, merge them
                new_start = last_start
                new_end = max(last_end, current_end)
                merged[-1] = (new_start, new_end)
            else:
                merged.append(interval)
    
    # Find free intervals by looking at gaps between busy intervals
    free_intervals = []
    previous_end = start_min
    for interval in merged:
        current_start, current_end = interval
        if current_start > previous_end:
            free_intervals.append((previous_end, current_start))
        previous_end = max(previous_end, current_end)
    
    # Check the interval after the last busy interval
    if previous_end < end_min:
        free_intervals.append((previous_end, end_min))
    
    # Now look for the first free interval that can accommodate the meeting duration
    duration = duration_minutes
    for interval in free_intervals:
        start, end = interval
        if end - start >= duration:
            # Found a suitable interval
            meeting_start = start
            meeting_end = meeting_start + duration
            # Convert back to hours and minutes
            start_hour = meeting_start // 60
            start_minute = meeting_start % 60
            end_hour = meeting_end // 60
            end_minute = meeting_end % 60
            return (
                f"{int(start_hour):02d}:{int(start_minute):02d}-{int(end_hour):02d}:{int(end_minute):02d}",
                day
            )
    
    return None, None

# Define the participants' schedules based on the given information
participants_schedules = [
    [],  # Ronald's calendar is wide open
    [(10, 10.5), (12, 12.5)],  # Stephen
    [(11, 11.5), (13.5, 14), (15.5, 16), (16.5, 17)],  # Brittany
    [(9, 9.5), (10, 10.5), (11, 12.5), (13, 15), (15.5, 17)],  # Dorothy
    [(9.5, 10.5), (11, 11.5), (12, 12.5), (13, 17)],  # Rebecca
    [(9, 9.5), (10, 11), (11.5, 12), (13, 15), (15.5, 16.5)],  # Jordan
]

# Define meeting parameters
day = "Monday"
work_hours_start = 9
work_hours_end = 17
duration_minutes = 30

# Find the meeting time
meeting_time, meeting_day = find_meeting_time(
    participants_schedules, day, work_hours_start, work_hours_end, duration_minutes
)

# Output the result
if meeting_time:
    print(f"Available meeting time: {meeting_time} on {meeting_day}")
else:
    print("No available meeting time found")