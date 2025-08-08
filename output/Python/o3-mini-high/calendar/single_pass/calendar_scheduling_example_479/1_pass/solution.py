def minutes_to_time(m):
    """Convert minutes since midnight to HH:MM format."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def merge_intervals(intervals):
    """Merge overlapping or contiguous intervals."""
    if not intervals:
        return []
    # Sort intervals by start time
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for current in intervals[1:]:
        last = merged[-1]
        # If the current interval overlaps or touches the last interval, merge them.
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def find_free_slot(merged_busy, work_start, work_end, duration):
    """Find the first free slot of at least 'duration' minutes within work hours."""
    free_slots = []
    # Check before the first busy interval.
    if work_start < merged_busy[0][0]:
        free_slots.append((work_start, merged_busy[0][0]))
    
    # Check between busy intervals.
    for i in range(len(merged_busy) - 1):
        end_current = merged_busy[i][1]
        start_next = merged_busy[i+1][0]
        free_slots.append((end_current, start_next))
    
    # Check after the last busy interval.
    if merged_busy[-1][1] < work_end:
        free_slots.append((merged_busy[-1][1], work_end))
    
    # Return the first free slot that is at least the given duration.
    for slot in free_slots:
        if slot[1] - slot[0] >= duration:
            return slot
    return None  # Should not happen per the problem constraints

def main():
    # Workday: 9:00 to 17:00 (in minutes since midnight)
    work_start = 9 * 60      # 540
    work_end   = 17 * 60     # 1020
    meeting_duration = 60    # one hour in minutes

    # Busy intervals for each participant (in minutes since midnight)
    # Evelyn and Kevin and Gerald are free all day so no intervals needed.
    busy_intervals = [
        # Joshua
        (11 * 60, 12 * 60 + 30),      # 11:00 - 12:30 -> (660, 750)
        (13 * 60 + 30, 14 * 60 + 30),  # 13:30 - 14:30 -> (810, 870)
        (16 * 60 + 30, 17 * 60),       # 16:30 - 17:00 -> (990, 1020)
        # Jerry
        (9 * 60, 9 * 60 + 30),         # 9:00 - 9:30 -> (540, 570)
        (10 * 60 + 30, 12 * 60),       # 10:30 - 12:00 -> (630, 720)
        (12 * 60 + 30, 13 * 60),       # 12:30 - 13:00 -> (750, 780)
        (13 * 60 + 30, 14 * 60),       # 13:30 - 14:00 -> (810, 840)
        (14 * 60 + 30, 15 * 60),       # 14:30 - 15:00 -> (870, 900)
        (15 * 60 + 30, 16 * 60),       # 15:30 - 16:00 -> (930, 960)
        # Jesse
        (9 * 60, 9 * 60 + 30),         # 9:00 - 9:30 -> (540, 570)
        (10 * 60 + 30, 12 * 60),       # 10:30 - 12:00 -> (630, 720)
        (12 * 60 + 30, 13 * 60),       # 12:30 - 13:00 -> (750, 780)
        (14 * 60 + 30, 15 * 60),       # 14:30 - 15:00 -> (870, 900)
        (15 * 60 + 30, 16 * 60 + 30),  # 15:30 - 16:30 -> (930, 990)
        # Kenneth
        (10 * 60 + 30, 12 * 60 + 30),  # 10:30 - 12:30 -> (630, 750)
        (13 * 60 + 30, 14 * 60),       # 13:30 - 14:00 -> (810, 840)
        (14 * 60 + 30, 15 * 60),       # 14:30 - 15:00 -> (870, 900)
        (15 * 60 + 30, 16 * 60),       # 15:30 - 16:00 -> (930, 960)
        (16 * 60 + 30, 17 * 60)        # 16:30 - 17:00 -> (990, 1020)
    ]

    # Merge busy intervals (note: some intervals overlap or touch)
    merged_busy = merge_intervals(busy_intervals)
    # For our inputs, merged_busy should end up as:
    # [(540, 570), (630, 780), (810, 900), (930, 1020)]
    
    # Find a free slot that can accommodate a one-hour meeting.
    free_slot = find_free_slot(merged_busy, work_start, work_end, meeting_duration)
    if free_slot:
        start_time = minutes_to_time(free_slot[0])
        end_time = minutes_to_time(free_slot[0] + meeting_duration)
        day = "Monday"
        print(f"{start_time}:{end_time}")
        print(day)
    else:
        print("No available slot found.")

if __name__ == "__main__":
    main()