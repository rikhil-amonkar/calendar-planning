def time_to_minutes(t):
    # t is "HH:MM"
    h, m = map(int, t.split(':'))
    return (h - 9) * 60 + m  # relative to 9:00

def minutes_to_time(m):
    # m is minutes from 9:00
    h = 9 + m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def parse_schedule(schedule_str, day):
    # schedule_str like "Monday during 9:30 to 10:00, 11:00 to 12:00, ..."
    # We extract only for given day
    intervals = []
    lines = schedule_str.split(';')
    for line in lines:
        if day in line:
            # Remove day and 'during'
            parts = line.strip().split('during')[1].strip()
            # parts = "9:30 to 10:00, 11:00 to 12:00, ..."
            pairs = parts.split(',')
            for p in pairs:
                p = p.strip()
                if 'to' in p:
                    start_str, end_str = p.split('to')
                    start = time_to_minutes(start_str.strip())
                    end = time_to_minutes(end_str.strip())
                    intervals.append((start, end))
    return intervals

def free_slots(busy_intervals, day_start=0, day_end=480):
    # day_start, day_end in minutes from 9:00
    if not busy_intervals:
        return [(day_start, day_end)]
    # Sort by start time
    sorted_intervals = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current_start = day_start
    for start, end in sorted_intervals:
        if start > current_start:
            free.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < day_end:
        free.append((current_start, day_end))
    return free

def intersect_slots(slots1, slots2, duration):
    # slots are lists of (start, end)
    common = []
    i = j = 0
    while i < len(slots1) and j < len(slots2):
        s1, e1 = slots1[i]
        s2, e2 = slots2[j]
        start = max(s1, s2)
        end = min(e1, e2)
        if start < end and end - start >= duration:
            common.append((start, end))
        if e1 < e2:
            i += 1
        else:
            j += 1
    return common

def main():
    ryan_schedule = (
        "Monday during 9:30 to 10:00, 11:00 to 12:00, 13:00 to 13:30, 15:30 to 16:00; "
        "Tuesday during 11:30 to 12:30, 15:30 to 16:00; "
        "Wednesday during 12:00 to 13:00, 15:30 to 16:00, 16:30 to 17:00"
    )
    adam_schedule = (
        "Monday during 9:00 to 10:30, 11:00 to 13:30, 14:00 to 16:00, 16:30 to 17:00; "
        "Tuesday during 9:00 to 10:00, 10:30 to 15:30, 16:00 to 17:00; "
        "Wednesday during 9:00 to 9:30, 10:00 to 11:00, 11:30 to 14:30, 15:00 to 15:30, 16:00 to 16:30"
    )
    
    days = ["Monday", "Tuesday", "Wednesday"]
    duration = 30  # minutes
    
    possible_slots = []
    
    for day in days:
        if day == "Wednesday":
            # Ryan cannot meet on Wednesday
            continue
        
        ryan_busy = parse_schedule(ryan_schedule, day)
        adam_busy = parse_schedule(adam_schedule, day)
        
        ryan_free = free_slots(ryan_busy, 0, 480)
        adam_free = free_slots(adam_busy, 0, 480)
        
        common = intersect_slots(ryan_free, adam_free, duration)
        
        for start, end in common:
            possible_slots.append((day, start, end))
    
    # Sort by day order (Monday, Tuesday) and start time
    day_order = {"Monday": 0, "Tuesday": 1, "Wednesday": 2}
    possible_slots.sort(key=lambda x: (day_order[x[0]], x[1]))
    
    # Apply Adam's preference: avoid Monday before 14:30 (14:30 = 5h30m from 9:00 = 330 minutes)
    # We'll try to find first slot that is not Monday before 14:30, else take first.
    chosen = None
    for day, start, end in possible_slots:
        if day == "Monday" and start < 330:
            continue  # skip Monday before 14:30
        chosen = (day, start, start + duration)
        break
    
    if chosen is None:
        # fallback to first possible slot
        chosen = (possible_slots[0][0], possible_slots[0][1], possible_slots[0][1] + duration)
    
    day, start_m, end_m = chosen
    start_time = minutes_to_time(start_m)
    end_time = minutes_to_time(end_m)
    
    # Output in format HH:MM:HH:MM
    print(f"{day}")
    print(f"{start_time}:{end_time}")

if __name__ == "__main__":
    main()