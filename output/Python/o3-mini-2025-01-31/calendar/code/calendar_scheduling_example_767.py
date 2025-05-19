def time_to_minutes(time_str):
    # Converts "HH:MM" to minutes since midnight
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    # Converts minutes since midnight to "HH:MM" formatted time string
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def subtract_busy_times(free_intervals, busy_intervals):
    result = []
    for free_start, free_end in free_intervals:
        current_start = free_start
        for busy_start, busy_end in busy_intervals:
            # If there is no intersection, continue.
            if busy_end <= current_start or busy_start >= free_end:
                continue
            # If there is an overlap, add free time before the busy block if exists
            if busy_start > current_start:
                result.append((current_start, busy_start))
            current_start = max(current_start, busy_end)
        # Add remaining part of free interval if any
        if current_start < free_end:
            result.append((current_start, free_end))
    return result

def intersect_intervals(intervals_a, intervals_b):
    intersection = []
    i, j = 0, 0
    while i < len(intervals_a) and j < len(intervals_b):
        start_a, end_a = intervals_a[i]
        start_b, end_b = intervals_b[j]
        # Find overlapping interval
        start_overlap = max(start_a, start_b)
        end_overlap = min(end_a, end_b)
        if start_overlap < end_overlap:
            intersection.append((start_overlap, end_overlap))
        # Move the pointer for the interval that ends first
        if end_a < end_b:
            i += 1
        else:
            j += 1
    return intersection

def find_meeting_time(meeting_duration):
    # Working hours: 09:00 to 17:00 in minutes from midnight
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    working_interval = [(work_start, work_end)]
    
    # Define busy intervals for each participant per day in minutes.
    # Format: { "Day": [(start, end), ...] }
    martha_busy = {
        "Monday": [(time_to_minutes("16:00"), time_to_minutes("17:00"))],
        "Tuesday": [(time_to_minutes("15:00"), time_to_minutes("15:30"))],
        "Wednesday": [(time_to_minutes("10:00"), time_to_minutes("11:00")),
                      (time_to_minutes("14:00"), time_to_minutes("14:30"))]
    }
    
    beverly_busy = {
        "Monday": [(time_to_minutes("09:00"), time_to_minutes("13:30")),
                   (time_to_minutes("14:00"), time_to_minutes("17:00"))],
        "Tuesday": [(time_to_minutes("09:00"), time_to_minutes("17:00"))],
        "Wednesday": [(time_to_minutes("09:30"), time_to_minutes("15:30")),
                      (time_to_minutes("16:30"), time_to_minutes("17:00"))]
    }
    
    # Try days in the order: Monday, Tuesday, Wednesday
    for day in ["Monday", "Tuesday", "Wednesday"]:
        # Compute free intervals by subtracting busy times from working hours
        martha_free = subtract_busy_times(working_interval, martha_busy.get(day, []))
        beverly_free = subtract_busy_times(working_interval, beverly_busy.get(day, []))
        
        # Find intersection of free times between Martha and Beverly
        common_free = intersect_intervals(martha_free, beverly_free)
        
        # Check each intersected interval for a slot that can fit the meeting_duration
        for start, end in common_free:
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = start + meeting_duration
                # Output in HH:MM:HH:MM format along with the day
                print(f"{day} {minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
                return

# Meeting duration 60 minutes
find_meeting_time(60)