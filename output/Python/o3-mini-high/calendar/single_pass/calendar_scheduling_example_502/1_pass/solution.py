def to_minutes(time_str):
    # Convert "HH:MM" to minutes since midnight.
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def format_time(minutes_val):
    # Format minutes-since-midnight into "HH:MM"
    hours = minutes_val // 60
    minutes = minutes_val % 60
    return f"{hours:02d}:{minutes:02d}"

def subtract_busy(available, busy_intervals):
    """
    Given an available interval (start, end) and a list of busy intervals (each a tuple (b_start, b_end)),
    returns a list of free intervals within available.
    """
    free = []
    current = available[0]
    for b_start, b_end in busy_intervals:
        if b_start > current:
            free.append((current, min(b_start, available[1])))
        current = max(current, b_end)
        if current >= available[1]:
            break
    if current < available[1]:
        free.append((current, available[1]))
    return free

def intersect_intervals(intervals1, intervals2):
    """
    Given two lists of intervals, returns a list with their intersection intervals.
    """
    i, j = 0, 0
    intersec = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        start_int = max(start1, start2)
        end_int = min(end1, end2)
        if start_int + 0 < end_int:  # if there is an overlap
            intersec.append((start_int, end_int))
        # Advance the interval that ends first.
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersec

def main():
    meeting_duration = 30  # in minutes
    day = "Monday"
    
    # Work hours are 09:00 to 17:00.
    # Jack prefers no meetings after 12:30 so we restrict our search to 09:00-12:30.
    window_start = to_minutes("09:00")
    window_end = to_minutes("12:30")  # meeting must finish by 12:30
    available_window = (window_start, window_end)
    
    # Busy schedules (given as strings) 
    # Jack is busy on Monday during:
    #   09:30-10:30, 11:00-11:30, 12:30-13:00, 14:00-14:30, 16:00-16:30.
    # Charlotte is busy on Monday during:
    #   09:30-10:00, 10:30-12:00, 12:30-13:30, 14:00-16:00.
    # We only care about those parts that affect our available window.
    jack_busy_raw = [("09:30", "10:30"), ("11:00", "11:30"),
                     ("12:30", "13:00"), ("14:00", "14:30"), ("16:00", "16:30")]
    charlotte_busy_raw = [("09:30", "10:00"), ("10:30", "12:00"),
                          ("12:30", "13:30"), ("14:00", "16:00")]
    
    def filter_intervals(raw_list, window):
        filtered = []
        for start, end in raw_list:
            start_min = to_minutes(start)
            end_min = to_minutes(end)
            # Only include busy intervals that intersect our available window.
            if end_min <= window[0] or start_min >= window[1]:
                continue
            filtered.append((max(start_min, window[0]), min(end_min, window[1])))
        return sorted(filtered)
    
    jack_busy = filter_intervals(jack_busy_raw, available_window)
    charlotte_busy = filter_intervals(charlotte_busy_raw, available_window)
    
    # Compute free slots for each participant within the available window.
    jack_free = subtract_busy(available_window, jack_busy)
    charlotte_free = subtract_busy(available_window, charlotte_busy)
    
    # Find the common free intervals.
    common_free = intersect_intervals(jack_free, charlotte_free)
    
    # Select the earliest slot that can hold a meeting of the required duration.
    meeting_slot = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break
            
    if meeting_slot:
        start_str = format_time(meeting_slot[0])
        end_str = format_time(meeting_slot[1])
        # The output is in the format: Day HH:MM:HH:MM (e.g., Monday 09:00:09:30)
        print(f"{day} {start_str}:{end_str}")
    else:
        print("No suitable slot found.")

if __name__ == '__main__':
    main()