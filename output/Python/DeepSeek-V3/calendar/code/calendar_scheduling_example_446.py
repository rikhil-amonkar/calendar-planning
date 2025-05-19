def find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes):
    # Convert work hours to minutes since midnight for easier calculation
    start_hour, start_minute = map(int, work_hours_start.split(':'))
    end_hour, end_minute = map(int, work_hours_end.split(':'))
    work_start = start_hour * 60 + start_minute
    work_end = end_hour * 60 + end_minute
    
    # Initialize a list to keep track of busy times for all participants
    busy_times = []
    
    for schedule in participants_schedules:
        for busy_range in schedule:
            start, end = busy_range.split(' to ')
            start_h, start_m = map(int, start.split(':'))
            end_h, end_m = map(int, end.split(':'))
            busy_start = start_h * 60 + start_m
            busy_end = end_h * 60 + end_m
            busy_times.append((busy_start, busy_end))
    
    # Sort all busy times by start time
    busy_times.sort()
    
    # Merge overlapping or adjacent busy times
    merged_busy = []
    for start, end in busy_times:
        if not merged_busy:
            merged_busy.append([start, end])
        else:
            last_start, last_end = merged_busy[-1]
            if start <= last_end:
                # Overlapping or adjacent, merge them
                merged_busy[-1][1] = max(end, last_end)
            else:
                merged_busy.append([start, end])
    
    # Find the earliest available slot
    prev_end = work_start
    for start, end in merged_busy:
        if start - prev_end >= duration_minutes:
            # Found a suitable slot
            meeting_start = prev_end
            meeting_end = meeting_start + duration_minutes
            # Convert back to HH:MM format
            start_hh = meeting_start // 60
            start_mm = meeting_start % 60
            end_hh = meeting_end // 60
            end_mm = meeting_end % 60
            return f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}", day
        prev_end = max(prev_end, end)
    
    # Check after the last busy time
    if work_end - prev_end >= duration_minutes:
        meeting_start = prev_end
        meeting_end = meeting_start + duration_minutes
        start_hh = meeting_start // 60
        start_mm = meeting_start % 60
        end_hh = meeting_end // 60
        end_mm = meeting_end % 60
        return f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}", day
    
    return None, day

# Define participants' schedules
participants_schedules = [
    ["9:00 to 9:30", "10:00 to 11:00", "12:00 to 12:30"],  # Megan
    ["9:00 to 9:30", "11:30 to 12:00", "13:00 to 14:00", "15:30 to 16:30"],  # Christine
    [],  # Gabriel
    ["11:30 to 12:00", "14:30 to 15:00"],  # Sara
    ["9:30 to 10:00", "10:30 to 12:00", "12:30 to 14:00", "14:30 to 15:00", "15:30 to 16:30"],  # Bruce
    ["10:00 to 15:30", "16:00 to 16:30"],  # Kathryn
    ["9:00 to 9:30", "11:00 to 11:30", "12:00 to 14:00", "14:30 to 15:30"],  # Billy
]

# Find a meeting time
meeting_time, day = find_meeting_time(participants_schedules, "Monday", "9:00", "17:00", 30)
print(f"{meeting_time}:{day}")