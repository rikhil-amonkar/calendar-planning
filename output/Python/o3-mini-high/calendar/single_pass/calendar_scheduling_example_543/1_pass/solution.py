def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(work_start, work_end, busy_intervals):
    free_intervals = []
    current_start = work_start
    for busy_start, busy_end in busy_intervals:
        if busy_start > current_start:
            free_intervals.append((current_start, busy_start))
        current_start = max(current_start, busy_end)
    if current_start < work_end:
        free_intervals.append((current_start, work_end))
    return free_intervals

def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        intersect_start = max(start1, start2)
        intersect_end = min(end1, end2)
        if intersect_end - intersect_start > 0:
            intersections.append((intersect_start, intersect_end))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

def find_meeting_slot(intersections, duration):
    for start, end in intersections:
        if end - start >= duration:
            return (start, start + duration)
    return None

def main():
    day = "Monday"
    meeting_duration = 60  # minutes
    work_start_str = "09:00"
    work_end_str = "17:00"
    
    work_start = time_to_minutes(work_start_str)
    work_end = time_to_minutes(work_end_str)
    
    # James is busy from 11:30 to 12:00 and 14:30 to 15:00
    james_busy_times = [("11:30", "12:00"), ("14:30", "15:00")]
    james_busy = [(time_to_minutes(start), time_to_minutes(end)) for start, end in james_busy_times]
    james_busy.sort()
    james_free = get_free_intervals(work_start, work_end, james_busy)
    
    # John is busy from 09:30 to 11:00, 11:30 to 12:00, 12:30 to 13:30, 14:30 to 16:30
    john_busy_times = [("09:30", "11:00"), ("11:30", "12:00"), ("12:30", "13:30"), ("14:30", "16:30")]
    john_busy = [(time_to_minutes(start), time_to_minutes(end)) for start, end in john_busy_times]
    john_busy.sort()
    john_free = get_free_intervals(work_start, work_end, john_busy)
    
    # Compute intersection of free intervals between James and John
    common_free = intersect_intervals(james_free, john_free)
    
    slot = find_meeting_slot(common_free, meeting_duration)
    
    if slot:
        start, end = slot
        start_str = minutes_to_time(start)
        end_str = minutes_to_time(end)
        # Output format: day HH:MM:HH:MM
        print(f"{day} {start_str}:{end_str}")
    else:
        print("No available meeting slot found.")

if __name__ == "__main__":
    main()