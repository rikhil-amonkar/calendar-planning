def find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes):
    # Convert all time slots to minutes since start of day for easier comparison
    start_time = work_hours_start * 60
    end_time = work_hours_end * 60
    duration = duration_minutes
    
    # Collect all busy intervals for all participants
    busy_intervals = []
    for schedule in participants_schedules:
        for busy in schedule:
            start = busy[0] * 60
            end = busy[1] * 60
            busy_intervals.append((start, end))
    
    # Sort all busy intervals by start time
    busy_intervals.sort()
    
    # Merge overlapping or adjacent busy intervals
    merged = []
    for start, end in busy_intervals:
        if not merged:
            merged.append((start, end))
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                # Overlapping or adjacent, merge them
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged[-1] = (new_start, new_end)
            else:
                merged.append((start, end))
    
    # Find the first available slot outside busy intervals
    previous_end = start_time
    for start, end in merged:
        if start > previous_end:
            available_start = previous_end
            available_end = start
            if available_end - available_start >= duration:
                # Found a suitable slot
                meeting_start = available_start
                meeting_end = meeting_start + duration
                return (meeting_start, meeting_end)
        previous_end = max(previous_end, end)
    
    # Check after the last busy interval
    if previous_end + duration <= end_time:
        meeting_start = previous_end
        meeting_end = meeting_start + duration
        return (meeting_start, meeting_end)
    
    # No available slot found (though the problem states one exists)
    return None

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define participants' schedules in 24-hour format as (start_hour, end_hour)
gregory = [(9, 9.5), (11.5, 12)]
jonathan = [(9, 9.5), (12, 12.5), (13, 13.5), (15, 16), (16.5, 17)]
barbara = [(10, 10.5), (13.5, 14)]
jesse = [(10, 11), (12.5, 14.5)]
alan = [(9.5, 11), (11.5, 12.5), (13, 15.5), (16, 17)]
nicole = [(9, 10.5), (11.5, 12), (12.5, 13.5), (14, 17)]
catherine = [(9, 10.5), (12, 13.5), (15, 15.5), (16, 16.5)]

# All participants' schedules
participants_schedules = [gregory, jonathan, barbara, jesse, alan, nicole, catherine]

# Find a meeting time
meeting_time = find_meeting_time(participants_schedules, "Monday", 9, 17, 30)

if meeting_time:
    start, end = meeting_time
    start_time_str = minutes_to_time(start)
    end_time_str = minutes_to_time(end)
    print(f"{start_time_str}:{end_time_str}")
    print("Monday")
else:
    print("No suitable time found.")