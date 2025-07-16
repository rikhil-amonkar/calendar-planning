def time_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def main():
    # Work hours and constraints
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    constraint_start = time_to_minutes("14:00")  # Wayne's constraint

    # Participants' busy schedules (each meeting as (start, end) in time strings)
    wayne_busy = []
    melissa_busy = [("10:00", "11:00"), ("12:30", "14:00"), ("15:00", "15:30")]
    catherine_busy = []
    gregory_busy = [("12:30", "13:00"), ("15:30", "16:00")]
    victoria_busy = [("9:00", "9:30"), ("10:30", "11:30"), ("13:00", "14:00"), ("14:30", "15:00"), ("15:30", "16:30")]
    thomas_busy = [("10:00", "12:00"), ("12:30", "13:00"), ("14:30", "16:00")]
    jennifer_busy = [("9:00", "9:30"), ("10:00", "10:30"), ("11:00", "13:00"), ("13:30", "14:30"), ("15:00", "15:30"), ("16:00", "16:30")]

    # Combine all busy intervals
    all_busy = []
    schedules = [wayne_busy, melissa_busy, catherine_busy, gregory_busy, victoria_busy, thomas_busy, jennifer_busy]
    
    for schedule in schedules:
        for (s_str, e_str) in schedule:
            s_min = time_to_minutes(s_str)
            e_min = time_to_minutes(e_str)
            # Clip to constraint_start and work_end
            if e_min <= constraint_start or s_min >= work_end:
                continue
            s_clip = max(s_min, constraint_start)
            e_clip = min(e_min, work_end)
            if e_clip > s_clip:
                all_busy.append((s_clip, e_clip))
    
    # If no busy intervals, entire constraint period is free
    if not all_busy:
        # Check if the constraint period is long enough
        if work_end - constraint_start >= 30:
            start_time = constraint_start
            end_time = start_time + 30
            print("Monday")
            print(f"{minutes_to_time(start_time)}:{minutes_to_time(end_time)}")
            return
        else:
            # Should not happen per problem statement
            print("Monday\nNo suitable time found")
            return
    
    # Sort and merge busy intervals
    all_busy.sort(key=lambda x: x[0])
    merged_busy = []
    current_start, current_end = all_busy[0]
    for i in range(1, len(all_busy)):
        s, e = all_busy[i]
        if s <= current_end:
            if e > current_end:
                current_end = e
        else:
            merged_busy.append((current_start, current_end))
            current_start, current_end = s, e
    merged_busy.append((current_start, current_end))
    
    # Find free intervals in [constraint_start, work_end]
    free_intervals = []
    # Before first busy interval
    if constraint_start < merged_busy[0][0]:
        free_intervals.append((constraint_start, merged_busy[0][0]))
    # Between busy intervals
    for i in range(len(merged_busy) - 1):
        free_start = merged_busy[i][1]
        free_end = merged_busy[i+1][0]
        if free_end > free_start:
            free_intervals.append((free_start, free_end))
    # After last busy interval
    if merged_busy[-1][1] < work_end:
        free_intervals.append((merged_busy[-1][1], work_end))
    
    # Find the first free interval of at least 30 minutes
    for s, e in free_intervals:
        if e - s >= 30:
            start_meeting = s
            end_meeting = s + 30
            print("Monday")
            print(f"{minutes_to_time(start_meeting)}:{minutes_to_time(end_meeting)}")
            return
    
    # Should not happen per problem statement
    print("Monday\nNo suitable time found")

if __name__ == "__main__":
    main()