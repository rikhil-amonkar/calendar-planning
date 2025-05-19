def time_to_minutes(time_str):
    # Convert "HH:MM" to number of minutes since midnight.
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    # Convert minutes since midnight to "HH:MM"
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy, work_start, work_end):
    # busy: list of tuples (start, end) in minutes, assumed sorted and non-overlapping
    free = []
    current = work_start
    for start, end in busy:
        if current < start:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(ints1, ints2):
    # Given two lists of intervals, compute intersection intervals.
    intersection = []
    i, j = 0, 0
    while i < len(ints1) and j < len(ints2):
        start1, end1 = ints1[i]
        start2, end2 = ints2[j]
        start = max(start1, start2)
        end = min(end1, end2)
        if start < end:  # non zero interval
            intersection.append((start, end))
        # Move the interval that ends first
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersection

def find_meeting_slot():
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Define working hours (in minutes since midnight)
    work_start = time_to_minutes("09:00")
    work_end   = time_to_minutes("17:00")
    
    # Allowed days in order of preference
    days = ["Monday", "Tuesday", "Wednesday"]
    
    # Schedules for participants in each day.
    # Times are in "HH:MM" format.
    # Tyler's busy schedule
    tyler_schedule = {
        "Monday": [ ],
        "Tuesday": [("09:00", "09:30"), ("14:30", "15:00")],
        "Wednesday": [("10:30", "11:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("16:30", "17:00")]
    }
    
    # Ruth's busy schedule
    ruth_schedule = {
        "Monday": [("09:00", "10:00"), ("10:30", "12:00"), ("12:30", "14:30"), ("15:00", "16:00"), ("16:30", "17:00")],
        "Tuesday": [("09:00", "17:00")],
        "Wednesday": [("09:00", "17:00")]
    }
    
    # Convert schedule times to minutes
    for schedule in (tyler_schedule, ruth_schedule):
        for day, intervals in schedule.items():
            schedule[day] = [(time_to_minutes(start), time_to_minutes(end)) for start, end in intervals]
            # Ensure intervals are sorted
            schedule[day].sort()
    
    # Tyler's preference: avoid meetings before 16:00 on Monday
    tyler_pref_monday_min = time_to_minutes("16:00")
    
    # For each day, determine free intervals for both participants and look for a slot
    for day in days:
        # Get free intervals for Tyler and Ruth
        tyler_free = get_free_intervals(tyler_schedule.get(day, []), work_start, work_end)
        ruth_free = get_free_intervals(ruth_schedule.get(day, []), work_start, work_end)
        
        # Compute common free intervals
        common_free = intersect_intervals(tyler_free, ruth_free)
        
        # If this is Monday, enforce Tyler's meeting preference:
        if day == "Monday":
            # For each free interval, bump the start time to max(interval_start, 16:00)
            adjusted = []
            for s, e in common_free:
                new_start = max(s, tyler_pref_monday_min)
                if new_start < e:
                    adjusted.append((new_start, e))
            common_free = adjusted

        # Check if any of these free intervals can host the meeting
        for start, end in common_free:
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = meeting_start + meeting_duration
                # Format the result as HH:MM:HH:MM and day of the week.
                start_str = minutes_to_time(meeting_start)
                end_str = minutes_to_time(meeting_end)
                print(f"{day} {start_str}:{end_str}")
                return

# Execute the scheduler
if __name__ == '__main__':
    find_meeting_slot()