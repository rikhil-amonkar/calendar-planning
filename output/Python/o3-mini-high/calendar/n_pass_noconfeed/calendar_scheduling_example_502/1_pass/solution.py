def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy, work_start, work_end):
    free_intervals = []
    current = work_start
    for start, end in busy:
        if current < start:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

def intersect_intervals(intervals1, intervals2, meeting_duration):
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        inter_start = max(start1, start2)
        inter_end = min(end1, end2)
        if inter_end - inter_start >= meeting_duration:
            intersections.append((inter_start, inter_end))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

def find_meeting_slot(common_free, meeting_duration, preferred_deadline):
    # Try to find a slot that ends on or before the preferred deadline.
    for start, end in common_free:
        if start + meeting_duration <= end and start + meeting_duration <= preferred_deadline:
            return start, start + meeting_duration
    # If none meets the preferred deadline, return the earliest available slot.
    for start, end in common_free:
        if start + meeting_duration <= end:
            return start, start + meeting_duration
    return None

def main():
    meeting_duration = 30  # minutes
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    
    # Jack's busy intervals on Monday
    jack_busy = [
        (time_to_minutes("09:30"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30")),
    ]
    
    # Charlotte's busy intervals on Monday
    charlotte_busy = [
        (time_to_minutes("09:30"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("16:00")),
    ]
    
    # Calculate free intervals within working hours
    free_jack = get_free_intervals(jack_busy, work_start, work_end)
    free_charlotte = get_free_intervals(charlotte_busy, work_start, work_end)
    
    # Determine common free time slots
    common_free = intersect_intervals(free_jack, free_charlotte, meeting_duration)
    
    # Jack prefers to have meetings finish by 12:30 (i.e., avoid meetings after 12:30)
    preferred_deadline = time_to_minutes("12:30")
    
    slot = find_meeting_slot(common_free, meeting_duration, preferred_deadline)
    
    if slot:
        start, end = slot
        day = "Monday"
        meeting_time = f"{minutes_to_time(start)}:{minutes_to_time(end)}"
        print(f"{day} {meeting_time}")
    else:
        print("No available meeting slot found.")

if __name__ == "__main__":
    main()