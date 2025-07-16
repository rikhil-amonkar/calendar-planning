def find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes):
    # Convert work hours to minutes since midnight for easier calculation
    start_time = work_hours_start * 60
    end_time = work_hours_end * 60
    
    # Initialize a list to keep track of busy intervals for all participants
    busy_intervals = []
    
    for schedule in participants_schedules:
        for meeting in schedule:
            start = meeting[0] * 60
            end = meeting[1] * 60
            busy_intervals.append((start, end))
    
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
    
    # Find available slots by checking gaps between merged intervals
    available_slots = []
    previous_end = start_time
    
    for interval in merged:
        current_start, current_end = interval
        if current_start > previous_end:
            # There's a gap between previous_end and current_start
            available_slots.append((previous_end, current_start))
        previous_end = max(previous_end, current_end)
    
    # Check the gap after the last busy interval until end_time
    if previous_end < end_time:
        available_slots.append((previous_end, end_time))
    
    # Find the first available slot that can fit the meeting duration
    duration = duration_minutes
    for slot in available_slots:
        slot_start, slot_end = slot
        if slot_end - slot_start >= duration:
            # Convert back to hours and minutes
            meeting_start = slot_start
            meeting_end = meeting_start + duration
            return (
                f"{meeting_start // 60:02d}:{meeting_start % 60:02d}:"
                f"{meeting_end // 60:02d}:{meeting_end % 60:02d}",
                day
            )
    
    return None, None

# Define participants' schedules in hours (as floats)
participants_schedules = [
    [(11.5, 12.0), (14.0, 14.5)],  # John
    [(12.0, 12.5), (14.0, 15.0), (15.5, 16.0)],  # Megan
    [],  # Brandon
    [(9.0, 9.5), (10.0, 10.5), (11.0, 14.5), (15.0, 16.0), (16.5, 17.0)],  # Kimberly
    [(10.0, 11.0), (11.5, 14.0), (15.0, 15.5)],  # Sean
    [(9.0, 9.5), (10.5, 12.0), (13.0, 14.5), (16.0, 16.5)],  # Lori
]

# Parameters
day = "Monday"
work_hours_start = 9.0
work_hours_end = 17.0
duration_minutes = 30  # half an hour

# Find the meeting time
time_range, day_of_week = find_meeting_time(
    participants_schedules, day, work_hours_start, work_hours_end, duration_minutes
)

# Output the result
print(f"{time_range}")
print(day_of_week)