def time_to_minutes(time_str):
    """Convert HH:MM string to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to HH:MM string."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def merge_intervals(intervals):
    """Merge overlapping intervals.
    Each interval is a tuple (start, end) in minutes.
    """
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = []
    for current in sorted_intervals:
        if not merged:
            merged.append(current)
        else:
            last = merged[-1]
            # If current interval overlaps or touches the last one, merge them.
            if current[0] <= last[1]:
                merged[-1] = (last[0], max(last[1], current[1]))
            else:
                merged.append(current)
    return merged

def get_free_intervals(merged_busy, work_start, work_end):
    """Given merged busy intervals within work hours, return free intervals."""
    free = []
    # If the first busy interval doesn't start at the work start, there is free time.
    if not merged_busy or work_start < merged_busy[0][0]:
        first_free_end = merged_busy[0][0] if merged_busy else work_end
        free.append((work_start, first_free_end))
    
    # Gaps between busy intervals
    for i in range(len(merged_busy) - 1):
        end_current = merged_busy[i][1]
        start_next = merged_busy[i+1][0]
        if start_next - end_current > 0:
            free.append((end_current, start_next))
    
    # After the last busy interval
    if merged_busy and merged_busy[-1][1] < work_end:
        free.append((merged_busy[-1][1], work_end))
    return free

def main():
    meeting_duration = 30  # in minutes
    day = "Monday"
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")

    # Define busy intervals for each participant (times in minutes from midnight)
    busy_intervals = []

    # Ronald: calendar wide open (no busy intervals)

    # Stephen: 10:00-10:30, 12:00-12:30
    busy_intervals.append((time_to_minutes("10:00"), time_to_minutes("10:30")))
    busy_intervals.append((time_to_minutes("12:00"), time_to_minutes("12:30")))

    # Brittany: 11:00-11:30, 13:30-14:00, 15:30-16:00, 16:30-17:00
    busy_intervals.append((time_to_minutes("11:00"), time_to_minutes("11:30")))
    busy_intervals.append((time_to_minutes("13:30"), time_to_minutes("14:00")))
    busy_intervals.append((time_to_minutes("15:30"), time_to_minutes("16:00")))
    busy_intervals.append((time_to_minutes("16:30"), time_to_minutes("17:00")))

    # Dorothy: 9:00-9:30, 10:00-10:30, 11:00-12:30, 13:00-15:00, 15:30-17:00
    busy_intervals.append((time_to_minutes("09:00"), time_to_minutes("09:30")))
    busy_intervals.append((time_to_minutes("10:00"), time_to_minutes("10:30")))
    busy_intervals.append((time_to_minutes("11:00"), time_to_minutes("12:30")))
    busy_intervals.append((time_to_minutes("13:00"), time_to_minutes("15:00")))
    busy_intervals.append((time_to_minutes("15:30"), time_to_minutes("17:00")))

    # Rebecca: 9:30-10:30, 11:00-11:30, 12:00-12:30, 13:00-17:00
    busy_intervals.append((time_to_minutes("09:30"), time_to_minutes("10:30")))
    busy_intervals.append((time_to_minutes("11:00"), time_to_minutes("11:30")))
    busy_intervals.append((time_to_minutes("12:00"), time_to_minutes("12:30")))
    busy_intervals.append((time_to_minutes("13:00"), time_to_minutes("17:00")))

    # Jordan: 9:00-9:30, 10:00-11:00, 11:30-12:00, 13:00-15:00, 15:30-16:30
    busy_intervals.append((time_to_minutes("09:00"), time_to_minutes("09:30")))
    busy_intervals.append((time_to_minutes("10:00"), time_to_minutes("11:00")))
    busy_intervals.append((time_to_minutes("11:30"), time_to_minutes("12:00")))
    busy_intervals.append((time_to_minutes("13:00"), time_to_minutes("15:00")))
    busy_intervals.append((time_to_minutes("15:30"), time_to_minutes("16:30")))

    # Merge all busy intervals
    merged_busy = merge_intervals(busy_intervals)
    
    # Get free intervals within the working hours
    free_intervals = get_free_intervals(merged_busy, work_start, work_end)
    
    # Find the first free interval that can accommodate the meeting_duration
    meeting_slot = None
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break

    if meeting_slot:
        start_str = minutes_to_time(meeting_slot[0])
        end_str = minutes_to_time(meeting_slot[1])
        # Output format: Day TimeRange (HH:MM:HH:MM)
        print(f"{day} {start_str}:{end_str}")
    else:
        print("No available time slot found.")

if __name__ == "__main__":
    main()