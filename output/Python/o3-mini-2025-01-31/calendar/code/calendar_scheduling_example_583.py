from datetime import datetime, timedelta

def time_to_minutes(time_str):
    # time_str is in "HH:MM" format
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    # busy_intervals is a list of tuples (start, end) in minutes, assumed sorted by start time
    free = []
    current = work_start
    for start, end in busy_intervals:
        if current < start:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    intersections = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # find the intersection between the two intervals
        intersect_start = max(start1, start2)
        intersect_end = min(end1, end2)
        if intersect_start < intersect_end:
            intersections.append((intersect_start, intersect_end))
        # move to the next interval in whichever ends earlier
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

def find_meeting_slot(intersections, duration):
    # duration in minutes, find earliest intersection that fits the meeting.
    for start, end in intersections:
        if end - start >= duration:
            return start, start + duration
    return None

def main():
    # Define constants
    work_day = "Monday"
    meeting_duration = 30  # minutes
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    
    # Define busy schedules for Lisa and Anthony in minutes
    lisa_busy = [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("14:00"), time_to_minutes("16:00"))
    ]
    
    anthony_busy = [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    
    # Compute free intervals
    lisa_free = get_free_intervals(lisa_busy, work_start, work_end)
    anthony_free = get_free_intervals(anthony_busy, work_start, work_end)
    
    # Get intersection of free intervals between Lisa and Anthony
    common_free = intersect_intervals(lisa_free, anthony_free)
    
    slot = find_meeting_slot(common_free, meeting_duration)
    
    if slot:
        meeting_start, meeting_end = slot
        print(f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
        print(work_day)
    else:
        print("No common available slot found.")

if __name__ == '__main__':
    main()