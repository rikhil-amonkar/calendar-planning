def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    """
    Given a list of busy intervals (each as [start, end] in minutes),
    returns a list of free intervals within the working period [work_start, work_end].
    """
    free = []
    # Sort busy intervals by start time.
    busy_intervals.sort(key=lambda x: x[0])
    
    # If there's free time before the first busy slot.
    if work_start < busy_intervals[0][0]:
        free.append([work_start, busy_intervals[0][0]])
    
    # Find gaps between busy intervals.
    for i in range(len(busy_intervals) - 1):
        if busy_intervals[i][1] < busy_intervals[i+1][0]:
            free.append([busy_intervals[i][1], busy_intervals[i+1][0]])
    
    # If there's free time after the last busy slot.
    if busy_intervals[-1][1] < work_end:
        free.append([busy_intervals[-1][1], work_end])
    
    return free

def intersect_intervals(intervals1, intervals2):
    """
    Given two lists of intervals, returns the list of intersections.
    """
    i = j = 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start < end:  # there is an overlap
            intersections.append([start, end])
        
        # Move the pointer that ends first.
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return intersections

def schedule_meeting():
    # Define the meeting day and working hours in minutes.
    day = "Monday"
    work_start = 9 * 60   # 9:00 AM -> 540 minutes
    work_end = 17 * 60    # 17:00 -> 1020 minutes
    
    meeting_duration = 60  # meeting duration is 60 minutes
    
    # Define busy schedules for Kayla and Rebecca in minutes.
    # Format for each busy interval: [start_time, end_time] in minutes.
    # Kayla's busy slots: 10:00-10:30 and 14:30-16:00.
    kayla_busy = [
        [10 * 60, 10 * 60 + 30],  # 10:00 to 10:30
        [14 * 60 + 30, 16 * 60]   # 14:30 to 16:00
    ]
    
    # Rebecca's busy slots: 9:00-13:00, 13:30-15:00, 15:30-16:00.
    rebecca_busy = [
        [9 * 60, 13 * 60],           # 9:00 to 13:00
        [13 * 60 + 30, 15 * 60],      # 13:30 to 15:00
        [15 * 60 + 30, 16 * 60]       # 15:30 to 16:00
    ]
    
    # Calculate free intervals for each participant.
    kayla_free = get_free_intervals(kayla_busy, work_start, work_end)
    rebecca_free = get_free_intervals(rebecca_busy, work_start, work_end)
    
    # Calculate overlapping free intervals between Kayla and Rebecca.
    common_free = intersect_intervals(kayla_free, rebecca_free)
    
    # Find the first common slot that can accommodate a 60-minute meeting.
    meeting_start = None
    meeting_end = None
    for interval in common_free:
        if interval[1] - interval[0] >= meeting_duration:
            meeting_start = interval[0]
            meeting_end = meeting_start + meeting_duration
            break
    
    if meeting_start is not None:
        start_time_str = minutes_to_time(meeting_start)
        end_time_str = minutes_to_time(meeting_end)
        # Output in the format HH:MM:HH:MM along with the day of the week.
        print(f"{start_time_str}:{end_time_str} {day}")
    else:
        print("No available slot found for a 60-minute meeting.")

if __name__ == "__main__":
    schedule_meeting()