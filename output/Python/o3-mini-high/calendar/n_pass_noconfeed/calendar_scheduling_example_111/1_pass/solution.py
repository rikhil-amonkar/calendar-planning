def minutes_to_str(m):
    """Convert minutes since midnight into HH:MM formatted string."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def intersect_intervals(intervals1, intervals2):
    """Return the intersection of two lists of intervals.
    Each interval is a tuple (start, end) where times are in minutes."""
    result = []
    for s1, e1 in intervals1:
        for s2, e2 in intervals2:
            start = max(s1, s2)
            end = min(e1, e2)
            if start < end:
                result.append((start, end))
    return result

def main():
    # Meeting parameters
    meeting_duration = 30  # in minutes
    day = "Monday"
    
    # Working hours in minutes (9:00 to 17:00)
    work_start = 9 * 60   # 540
    work_end = 17 * 60    # 1020

    # Define free intervals for each participant as (start, end) in minutes.
    # Gregory: busy: [9:00-10:00], [10:30-11:30], [12:30-13:00], [13:30-14:00]
    # => free intervals:
    gregory_free = [
        (10 * 60, 10 * 60 + 30),    # 10:00-10:30  -> (600,630)
        (11 * 60 + 30, 12 * 60 + 30), # 11:30-12:30 -> (690,750)
        (13 * 60, 13 * 60 + 30),      # 13:00-13:30 -> (780,810)
        (14 * 60, work_end)          # 14:00-17:00 -> (840,1020)
    ]
    
    # Natalie is free the entire day.
    natalie_free = [(work_start, work_end)]
    
    # Christine: busy: [9:00-11:30], [13:30-17:00]
    # => free interval:
    christine_free = [
        (11 * 60 + 30, 13 * 60 + 30)  # 11:30-13:30 -> (690,810)
    ]
    
    # Vincent: busy: [9:00-9:30], [10:30-12:00], 
    #          [12:30-14:00], [14:30-17:00]
    # => free intervals:
    vincent_free = [
        (9 * 60 + 30, 10 * 60 + 30),   # 9:30-10:30 -> (570,630)
        (12 * 60, 12 * 60 + 30),         # 12:00-12:30 -> (720,750)
        (14 * 60, 14 * 60 + 30)          # 14:00-14:30 -> (840,870)
    ]
    
    # Find common free intervals by intersecting free times for all participants.
    common_free = intersect_intervals(gregory_free, natalie_free)
    common_free = intersect_intervals(common_free, christine_free)
    common_free = intersect_intervals(common_free, vincent_free)
    
    # Find the first interval that can accommodate the meeting duration.
    meeting_start = None
    meeting_end = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            break

    if meeting_start is not None:
        start_str = minutes_to_str(meeting_start)
        end_str = minutes_to_str(meeting_end)
        # Output in the format HH:MM:HH:MM along with the day of the week.
        print(f"{day} {start_str}:{end_str}")
    else:
        print("No common time slot available.")

if __name__ == "__main__":
    main()