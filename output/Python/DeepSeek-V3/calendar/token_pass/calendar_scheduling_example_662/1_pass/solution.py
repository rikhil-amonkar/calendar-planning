def time_to_minutes(t):
    """Convert HH:MM to minutes since midnight."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes since midnight to HH:MM string."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def parse_blocked(blocked_str):
    """Parse blocked times like '9:30 to 10:00' into (start_min, end_min)."""
    times = []
    parts = blocked_str.replace(' to ', '-').split('-')
    for i in range(0, len(parts), 2):
        start = time_to_minutes(parts[i])
        end = time_to_minutes(parts[i+1])
        times.append((start, end))
    return times

def find_free_slots(blocked_list, day_start, day_end):
    """Given blocked times in minutes, return free slots."""
    blocked = sorted(blocked_list, key=lambda x: x[0])
    free = []
    current = day_start
    for start, end in blocked:
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < day_end:
        free.append((current, day_end))
    return free

def intersect_slots(slots1, slots2, duration):
    """Find common slots of at least given duration (in minutes)."""
    common = []
    i = j = 0
    while i < len(slots1) and j < len(slots2):
        start = max(slots1[i][0], slots2[j][0])
        end = min(slots1[i][1], slots2[j][1])
        if start < end:
            common.append((start, end))
        if slots1[i][1] < slots2[j][1]:
            i += 1
        else:
            j += 1
    
    # Now split into duration chunks
    result = []
    for s, e in common:
        if e - s >= duration:
            result.append((s, e))
    return result

def main():
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 60  # minutes
    
    # Blocked times in minutes
    gary_monday = [
        (time_to_minutes("9:30"), time_to_minutes("10:00")),
        (time_to_minutes("11:00"), time_to_minutes("13:00")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    gary_tuesday = [
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("14:30"), time_to_minutes("16:00"))
    ]
    david_monday = [
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("10:00"), time_to_minutes("13:00")),
        (time_to_minutes("14:30"), time_to_minutes("16:30"))
    ]
    david_tuesday = [
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    
    # Free slots
    gary_free_mon = find_free_slots(gary_monday, work_start, work_end)
    gary_free_tue = find_free_slots(gary_tuesday, work_start, work_end)
    david_free_mon = find_free_slots(david_monday, work_start, work_end)
    david_free_tue = find_free_slots(david_tuesday, work_start, work_end)
    
    # Intersect
    mon_common = intersect_slots(gary_free_mon, david_free_mon, meeting_duration)
    tue_common = intersect_slots(gary_free_tue, david_free_tue, meeting_duration)
    
    # Output first found slot
    if mon_common:
        start, end = mon_common[0]
        print(f"Monday {minutes_to_time(start)}:{minutes_to_time(start + meeting_duration)}")
    elif tue_common:
        start, end = tue_common[0]
        print(f"Tuesday {minutes_to_time(start)}:{minutes_to_time(start + meeting_duration)}")
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()