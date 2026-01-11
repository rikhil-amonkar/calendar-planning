def time_to_minutes(t):
    """Convert 'HH:MM' to minutes since midnight."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes since midnight to 'HH:MM'."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def merge_intervals(intervals):
    """Merge overlapping intervals."""
    if not intervals:
        return []
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for start, end in intervals[1:]:
        last_start, last_end = merged[-1]
        if start <= last_end:
            merged[-1] = (last_start, max(last_end, end))
        else:
            merged.append((start, end))
    return merged

def main():
    # Work hours on Monday
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    
    # Busy times for each person (in minutes since midnight)
    busy_times = [
        # Gregory
        [(time_to_minutes("9:00"), time_to_minutes("9:30")),
         (time_to_minutes("11:30"), time_to_minutes("12:00"))],
        # Jonathan
        [(time_to_minutes("9:00"), time_to_minutes("9:30")),
         (time_to_minutes("12:00"), time_to_minutes("12:30")),
         (time_to_minutes("13:00"), time_to_minutes("13:30")),
         (time_to_minutes("15:00"), time_to_minutes("16:00")),
         (time_to_minutes("16:30"), time_to_minutes("17:00"))],
        # Barbara
        [(time_to_minutes("10:00"), time_to_minutes("10:30")),
         (time_to_minutes("13:30"), time_to_minutes("14:00"))],
        # Jesse
        [(time_to_minutes("10:00"), time_to_minutes("11:00")),
         (time_to_minutes("12:30"), time_to_minutes("14:30"))],
        # Alan
        [(time_to_minutes("9:30"), time_to_minutes("11:00")),
         (time_to_minutes("11:30"), time_to_minutes("12:30")),
         (time_to_minutes("13:00"), time_to_minutes("15:30")),
         (time_to_minutes("16:00"), time_to_minutes("17:00"))],
        # Nicole
        [(time_to_minutes("9:00"), time_to_minutes("10:30")),
         (time_to_minutes("11:30"), time_to_minutes("12:00")),
         (time_to_minutes("12:30"), time_to_minutes("13:30")),
         (time_to_minutes("14:00"), time_to_minutes("17:00"))],
        # Catherine
        [(time_to_minutes("9:00"), time_to_minutes("10:30")),
         (time_to_minutes("12:00"), time_to_minutes("13:30")),
         (time_to_minutes("15:00"), time_to_minutes("15:30")),
         (time_to_minutes("16:00"), time_to_minutes("16:30"))],
    ]
    
    # Combine all busy intervals
    all_busy = []
    for person in busy_times:
        all_busy.extend(person)
    
    # Merge intervals
    merged_busy = merge_intervals(all_busy)
    
    # Add work hour boundaries as busy times before start and after end
    # to easily find free slots inside work hours
    merged_busy = [(work_start, work_start)] + merged_busy + [(work_end, work_end)]
    merged_busy = merge_intervals(merged_busy)
    
    # Find free slots (gaps between busy times)
    free_slots = []
    for i in range(len(merged_busy) - 1):
        end_current = merged_busy[i][1]
        start_next = merged_busy[i + 1][0]
        if start_next - end_current >= 30:  # 30 minutes meeting
            free_slots.append((end_current, start_next))
    
    # Filter slots that are within work hours
    valid_slots = []
    for start, end in free_slots:
        if start >= work_start and end <= work_end:
            valid_slots.append((start, end))
    
    # Output the first valid slot
    if valid_slots:
        meeting_start = valid_slots[0][0]
        meeting_end = meeting_start + 30
        print(f"Monday:{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()