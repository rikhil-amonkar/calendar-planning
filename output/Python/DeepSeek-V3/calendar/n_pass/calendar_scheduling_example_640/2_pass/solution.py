def find_meeting_time(bobby_schedule, michael_schedule, work_hours, meeting_duration, days):
    # Convert time strings to minutes since 9:00 (start of work hours)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return (hh - 9) * 60 + mm  # Assuming work hours start at 9:00
    
    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = 9 + int(minutes) // 60  # Ensure integer division
        mm = int(minutes) % 60       # Ensure modulo with integer
        return f"{hh:02d}:{mm:02d}"
    
    # Generate busy intervals in minutes for a given day
    def get_busy_intervals(schedule, day):
        day_schedule = schedule.get(day, [])
        intervals = []
        for interval in day_schedule:
            start, end = interval.split(' to ')
            start_min = time_to_minutes(start)
            end_min = time_to_minutes(end)
            intervals.append((start_min, end_min))
        return intervals
    
    # Find available slots by merging busy intervals
    def find_available_slots(busy_intervals, work_hours_start, work_hours_end):
        if not busy_intervals:
            return [(work_hours_start, work_hours_end)]
        
        # Sort intervals by start time
        busy_intervals.sort()
        merged = []
        current_start, current_end = busy_intervals[0]
        
        for start, end in busy_intervals[1:]:
            if start <= current_end:
                current_end = max(current_end, end)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = start, end
        merged.append((current_start, current_end))
        
        # Find available slots between merged intervals
        available = []
        prev_end = work_hours_start
        for start, end in merged:
            if start > prev_end:
                available.append((prev_end, start))
            prev_end = max(prev_end, end)
        if prev_end < work_hours_end:
            available.append((prev_end, work_hours_end))
        
        return available
    
    work_hours_start = time_to_minutes(work_hours[0])
    work_hours_end = time_to_minutes(work_hours[1])
    meeting_duration_min = int(meeting_duration * 60)  # Ensure integer minutes
    
    for day in days:
        # Get busy intervals for Bobby and Michael
        bobby_busy = get_busy_intervals(bobby_schedule, day)
        michael_busy = get_busy_intervals(michael_schedule, day)
        
        # Find available slots for each
        bobby_available = find_available_slots(bobby_busy, work_hours_start, work_hours_end)
        michael_available = find_available_slots(michael_busy, work_hours_start, work_hours_end)
        
        # Find overlapping available slots
        for b_start, b_end in bobby_available:
            for m_start, m_end in michael_available:
                overlap_start = max(b_start, m_start)
                overlap_end = min(b_end, m_end)
                if overlap_end - overlap_start >= meeting_duration_min:
                    # Found a suitable slot
                    start_time = minutes_to_time(overlap_start)
                    end_time = minutes_to_time(overlap_start + meeting_duration_min)
                    return day, f"{start_time} to {end_time}"
    
    return None, None

# Define schedules
bobby_schedule = {
    "Monday": ["14:30 to 15:00"],
    "Tuesday": ["9:00 to 11:30", "12:00 to 12:30", "13:00 to 15:00", "15:30 to 17:00"]
}

michael_schedule = {
    "Monday": ["9:00 to 10:00", "10:30 to 13:30", "14:00 to 15:00", "15:30 to 17:00"],
    "Tuesday": ["9:00 to 10:30", "11:00 to 11:30", "12:00 to 14:00", "15:00 to 16:00", "16:30 to 17:00"]
}

# Define parameters
work_hours = ("9:00", "17:00")
meeting_duration = 0.5  # in hours
days = ["Monday", "Tuesday"]

# Find meeting time
day, time_range = find_meeting_time(bobby_schedule, michael_schedule, work_hours, meeting_duration, days)

# Output the result
if day and time_range:
    print(f"{day}, {time_range}")
else:
    print("No available meeting time found")