def time_to_minutes(time_str):
    """Converts a HH:MM time string to total minutes."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Converts total minutes into a HH:MM string."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_slots(blocked, work_start, work_end):
    """
    Given a list of blocked intervals (each a tuple (start, end) in minutes),
    return a list of free intervals within the working hours.
    """
    free = []
    current = work_start
    for start, end in sorted(blocked):
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(slots1, slots2):
    """Intersects two lists of intervals (in minutes) and returns the overlapping intervals."""
    intersections = []
    i, j = 0, 0
    while i < len(slots1) and j < len(slots2):
        start = max(slots1[i][0], slots2[j][0])
        end = min(slots1[i][1], slots2[j][1])
        if start < end:
            intersections.append((start, end))
        # Move to the next interval in the schedule that ends first.
        if slots1[i][1] < slots2[j][1]:
            i += 1
        else:
            j += 1
    return intersections

def find_meeting_slot(intersections, duration):
    """Finds the first intersection slot that can fit the meeting duration."""
    for start, end in intersections:
        if end - start >= duration:
            return start, start + duration
    return None

if __name__ == "__main__":
    # Meeting and working hours details
    meeting_duration = 60  # meeting duration in minutes (1 hour)
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    day_of_week = "Monday"
    
    # Blocked intervals for each participant (in minutes)
    # Kayla: 10:00-10:30 and 14:30-16:00
    kayla_blocked = [
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("14:30"), time_to_minutes("16:00"))
    ]
    
    # Rebecca: 9:00-13:00, 13:30-15:00, and 15:30-16:00
    rebecca_blocked = [
        (time_to_minutes("09:00"), time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00"))
    ]
    
    # Calculate free slots for each participant within working hours
    kayla_free = get_free_slots(kayla_blocked, work_start, work_end)
    rebecca_free = get_free_slots(rebecca_blocked, work_start, work_end)
    
    # Find the intersections of free slots between Kayla and Rebecca
    common_free = intersect_intervals(kayla_free, rebecca_free)
    
    meeting_slot = find_meeting_slot(common_free, meeting_duration)
    
    if meeting_slot:
        start_time = minutes_to_time(meeting_slot[0])
        end_time = minutes_to_time(meeting_slot[1])
        # Output in the format HH:MM:HH:MM along with the day
        # For example: Monday {16:00:17:00}
        print(day_of_week)
        print(f"{{{start_time}:{end_time}}}")
    else:
        print("No available slot found.")