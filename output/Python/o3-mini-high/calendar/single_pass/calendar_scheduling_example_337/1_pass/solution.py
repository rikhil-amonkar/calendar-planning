def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    free = []
    current = work_start
    for start, end in busy_intervals:
        if start > current:
            free.append((current, start))
        if end > current:
            current = end
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_two_intervals(list1, list2):
    i, j = 0, 0
    result = []
    while i < len(list1) and j < len(list2):
        start1, end1 = list1[i]
        start2, end2 = list2[j]
        # Find the overlapping interval
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            result.append((start_overlap, end_overlap))
        # Move forward in the list that ends earlier
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

def intersect_intervals(lists):
    if not lists:
        return []
    common = lists[0]
    for other in lists[1:]:
        common = intersect_two_intervals(common, other)
        if not common:
            break
    return common

def main():
    meeting_day = "Monday"
    meeting_duration = 30  # minutes
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    
    # Busy schedules for each participant as (start, end) in "HH:MM" format
    schedules = {
        "John": [("11:30", "12:00"), ("14:00", "14:30")],
        "Megan": [("12:00", "12:30"), ("14:00", "15:00"), ("15:30", "16:00")],
        "Brandon": [],  # No meetings
        "Kimberly": [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "14:30"), ("15:00", "16:00"), ("16:30", "17:00")],
        "Sean": [("10:00", "11:00"), ("11:30", "14:00"), ("15:00", "15:30")],
        "Lori": [("09:00", "09:30"), ("10:30", "12:00"), ("13:00", "14:30"), ("16:00", "16:30")]
    }
    
    # Convert busy times to minutes and sort them for each person
    free_intervals_all = []
    for person, times in schedules.items():
        busy = sorted([(time_to_minutes(start), time_to_minutes(end)) for start, end in times])
        free = get_free_intervals(busy, work_start, work_end)
        free_intervals_all.append(free)
    
    # Compute the common free intervals for all participants
    common_free = intersect_intervals(free_intervals_all)
    
    # Find the first interval that can accommodate the meeting duration
    meeting_slot = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break
            
    if meeting_slot:
        start_str = minutes_to_time(meeting_slot[0])
        end_str = minutes_to_time(meeting_slot[1])
        # Output format: HH:MM:HH:MM along with the day
        print(f"{meeting_day} {start_str}:{end_str}")
    else:
        print("No common free slot found.")

if __name__ == "__main__":
    main()