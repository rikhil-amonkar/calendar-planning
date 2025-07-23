def find_meeting_time(participants_schedules, work_hours_start, work_hours_end, duration_minutes, day):
    # Convert all times to minutes since midnight for easier comparison
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    duration = duration_minutes
    
    # Collect all busy intervals for all participants
    busy_intervals = []
    for schedule in participants_schedules:
        for interval in schedule:
            start, end = map(time_to_minutes, interval.split(' to '))
            busy_intervals.append((start, end))
    
    # Sort all busy intervals by start time
    busy_intervals.sort()
    
    # Find the earliest available slot
    current_time = work_start
    for start, end in busy_intervals:
        if start > current_time:
            # Check if the gap is enough for the meeting
            if start - current_time >= duration:
                meeting_end = current_time + duration
                # Convert back to HH:MM format
                def minutes_to_time(minutes):
                    hh = minutes // 60
                    mm = minutes % 60
                    return f"{hh:02d}:{mm:02d}"
                return f"{minutes_to_time(current_time)}:{minutes_to_time(meeting_end)}"
            else:
                current_time = end
        else:
            if end > current_time:
                current_time = end
        if current_time >= work_end:
            break
    
    # Check the remaining time after the last busy interval
    if work_end - current_time >= duration:
        meeting_end = current_time + duration
        def minutes_to_time(minutes):
            hh = minutes // 60
            mm = minutes % 60
            return f"{hh:02d}:{mm:02d}"
        return f"{minutes_to_time(current_time)}:{minutes_to_time(meeting_end)}"
    else:
        return None

# Define the participants' schedules
denise_schedule = ["12:00 to 12:30", "15:30 to 16:00"]
angela_schedule = []
natalie_schedule = ["9:00 to 11:30", "12:00 to 13:00", "14:00 to 14:30", "15:00 to 17:00"]

# Combine all schedules
participants_schedules = [denise_schedule, angela_schedule, natalie_schedule]

# Define work hours and meeting duration
work_hours_start = "9:00"
work_hours_end = "17:00"
duration_minutes = 30
day = "Monday"

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, work_hours_start, work_hours_end, duration_minutes, day)

# Output the result
print(f"{day}:{meeting_time}")