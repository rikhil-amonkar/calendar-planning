def find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes):
    # Convert work hours to minutes since midnight for easier calculation
    start_time = work_hours_start.hour * 60 + work_hours_start.minute
    end_time = work_hours_end.hour * 60 + work_hours_end.minute
    
    # Initialize a list to keep track of busy intervals for all participants
    busy_intervals = []
    
    # Collect all busy intervals from each participant's schedule
    for schedule in participants_schedules:
        for busy in schedule:
            busy_start = busy[0].hour * 60 + busy[0].minute
            busy_end = busy[1].hour * 60 + busy[1].minute
            busy_intervals.append((busy_start, busy_end))
    
    # Sort the busy intervals by start time
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
                new_end = max(last_end, current_end)
                merged[-1] = (last_start, new_end)
            else:
                merged.append(interval)
    
    # Find the first available slot that fits the duration
    previous_end = start_time
    for interval in merged:
        current_start, current_end = interval
        if current_start - previous_end >= duration_minutes:
            # Found a suitable slot
            meeting_start = previous_end
            meeting_end = meeting_start + duration_minutes
            return (
                day,
                f"{meeting_start // 60:02d}:{meeting_start % 60:02d}:{meeting_end // 60:02d}:{meeting_end % 60:02d}"
            )
        previous_end = max(previous_end, current_end)
    
    # Check the slot after the last busy interval
    if end_time - previous_end >= duration_minutes:
        meeting_start = previous_end
        meeting_end = meeting_start + duration_minutes
        return (
            day,
            f"{meeting_start // 60:02d}:{meeting_start % 60:02d}:{meeting_end // 60:02d}:{meeting_end % 60:02d}"
        )
    
    # No suitable slot found (though the problem states there is one)
    return None

# Define the participants' schedules
from datetime import time

participants_schedules = [
    # Andrea
    [(time(9, 30), time(10, 30)), (time(13, 30), time(14, 30))],
    # Ruth
    [(time(12, 30), time(13, 0)), (time(15, 0), time(15, 30))],
    # Steven
    [(time(10, 0), time(10, 30)), (time(11, 0), time(11, 30)), (time(12, 0), time(12, 30)), (time(13, 30), time(14, 0)), (time(15, 0), time(16, 0))],
    # Grace
    [],
    # Kyle
    [(time(9, 0), time(9, 30)), (time(10, 30), time(12, 0)), (time(12, 30), time(13, 0)), (time(13, 30), time(15, 0)), (time(15, 30), time(16, 0)), (time(16, 30), time(17, 0))],
    # Elijah
    [(time(9, 0), time(11, 0)), (time(11, 30), time(13, 0)), (time(13, 30), time(14, 0)), (time(15, 30), time(16, 0)), (time(16, 30), time(17, 0))],
    # Lori
    [(time(9, 0), time(9, 30)), (time(10, 0), time(11, 30)), (time(12, 0), time(13, 30)), (time(14, 0), time(16, 0)), (time(16, 30), time(17, 0))],
]

# Find the meeting time
day = "Monday"
work_hours_start = time(9, 0)
work_hours_end = time(17, 0)
duration_minutes = 30

result = find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes)
if result:
    day, time_range = result
    print(f"{day}: {time_range}")
else:
    print("No suitable time found.")