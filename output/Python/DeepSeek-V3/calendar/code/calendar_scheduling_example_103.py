def find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes):
    # Convert all time slots to minutes since start of the day for easier calculation
    start_work = work_hours_start[0] * 60 + work_hours_start[1]
    end_work = work_hours_end[0] * 60 + work_hours_end[1]
    
    # Initialize the list of busy intervals for all participants
    busy_intervals = []
    
    for schedule in participants_schedules:
        for block in schedule:
            start_block = block[0][0] * 60 + block[0][1]
            end_block = block[1][0] * 60 + block[1][1]
            busy_intervals.append((start_block, end_block))
    
    # Sort all busy intervals by start time
    busy_intervals.sort()
    
    # Find the earliest available slot
    current_time = start_work
    available_slot_end = current_time + duration_minutes
    
    for start, end in busy_intervals:
        if start > current_time:
            if available_slot_end <= start:
                # Found a suitable slot
                break
            else:
                current_time = end
                available_slot_end = current_time + duration_minutes
        else:
            if current_time < end:
                current_time = end
                available_slot_end = current_time + duration_minutes
    
    # Check if the slot is within work hours
    if available_slot_end <= end_work:
        # Convert back to HH:MM format
        start_hh = current_time // 60
        start_mm = current_time % 60
        end_hh = available_slot_end // 60
        end_mm = available_slot_end % 60
        return f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
    else:
        return None

# Define participants' schedules in HH:MM format
diane_schedule = [
    [(9, 30), (10, 0)],
    [(14, 30), (15, 0)]
]
jack_schedule = [
    [(13, 30), (14, 0)],
    [(14, 30), (15, 0)]
]
eugene_schedule = [
    [(9, 0), (10, 0)],
    [(10, 30), (11, 30)],
    [(12, 0), (14, 30)],
    [(15, 0), (16, 30)]
]
patricia_schedule = [
    [(9, 30), (10, 30)],
    [(11, 0), (12, 0)],
    [(12, 30), (14, 0)],
    [(15, 0), (16, 30)]
]

participants_schedules = [diane_schedule, jack_schedule, eugene_schedule, patricia_schedule]
day = "Monday"
work_hours_start = (9, 0)
work_hours_end = (17, 0)
duration_minutes = 30

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes)

# Output the result
print(f"{meeting_time}:{day}")