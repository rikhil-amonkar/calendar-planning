def time_to_minutes(t):
    """Convert 'HH:MM' to minutes from 9:00."""
    h, m = map(int, t.split(':'))
    return (h - 9) * 60 + m

def minutes_to_time(m):
    """Convert minutes from 9:00 to 'HH:MM'."""
    h = 9 + m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def add_busy(busy_dict, day, start_str, end_str):
    busy_dict[day].append((time_to_minutes(start_str), time_to_minutes(end_str)))

def find_free_slots(busy_slots, day_start, day_end, duration):
    """Find free slots within day_start to day_end given busy slots."""
    busy_slots.sort()
    free = []
    last_end = day_start
    for start, end in busy_slots:
        if start > last_end:
            free.append((last_end, start))
        last_end = max(last_end, end)
    if last_end < day_end:
        free.append((last_end, day_end))
    # Filter for duration
    result = []
    for s, e in free:
        if e - s >= duration:
            result.append((s, e))
    return result

def intersect_slots(slots1, slots2, duration):
    """Intersect two lists of free slots and keep only those with min duration."""
    i, j = 0, 0
    intersections = []
    while i < len(slots1) and j < len(slots2):
        s1, e1 = slots1[i]
        s2, e2 = slots2[j]
        start = max(s1, s2)
        end = min(e1, e2)
        if start < end and end - start >= duration:
            intersections.append((start, end))
        if e1 < e2:
            i += 1
        else:
            j += 1
    return intersections

def main():
    # Work hours: 9:00 to 17:00 -> in minutes from 9:00: 0 to 480
    DAY_START = 0
    DAY_END = 480
    DURATION = 60  # 1 hour in minutes

    days = ["Monday", "Tuesday"]
    patricia_busy = {day: [] for day in days}
    jesse_busy = {day: [] for day in days}

    # Patricia's meetings
    # Monday
    add_busy(patricia_busy, "Monday", "10:00", "10:30")
    add_busy(patricia_busy, "Monday", "11:30", "12:00")
    add_busy(patricia_busy, "Monday", "13:00", "13:30")
    add_busy(patricia_busy, "Monday", "14:30", "15:30")
    add_busy(patricia_busy, "Monday", "16:00", "16:30")
    # Tuesday
    add_busy(patricia_busy, "Tuesday", "10:00", "10:30")
    add_busy(patricia_busy, "Tuesday", "11:00", "12:00")
    add_busy(patricia_busy, "Tuesday", "14:00", "16:00")
    add_busy(patricia_busy, "Tuesday", "16:30", "17:00")

    # Jesse's meetings
    # Monday
    add_busy(jesse_busy, "Monday", "9:00", "17:00")  # whole day blocked
    # Tuesday
    add_busy(jesse_busy, "Tuesday", "11:00", "11:30")
    add_busy(jesse_busy, "Tuesday", "12:00", "12:30")
    add_busy(jesse_busy, "Tuesday", "13:00", "14:00")
    add_busy(jesse_busy, "Tuesday", "14:30", "15:00")
    add_busy(jesse_busy, "Tuesday", "15:30", "17:00")

    # Find slots
    for day in days:
        patricia_free = find_free_slots(patricia_busy[day], DAY_START, DAY_END, DURATION)
        jesse_free = find_free_slots(jesse_busy[day], DAY_START, DAY_END, DURATION)
        common = intersect_slots(patricia_free, jesse_free, DURATION)
        if common:
            # Take the first common slot
            start_min, end_min = common[0]
            start_time = minutes_to_time(start_min)
            end_time = minutes_to_time(end_min)
            print(f"{day}:{start_time}:{end_time}")
            return
    print("No suitable slot found")

if __name__ == "__main__":
    main()