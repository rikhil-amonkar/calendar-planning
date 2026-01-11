from datetime import datetime, timedelta

def time_to_minutes(t):
    """Convert 'HH:MM' to minutes since midnight."""
    return t.hour * 60 + t.minute

def minutes_to_time_str(m):
    """Convert minutes since midnight to 'HH:MM' string."""
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def parse_busy_ranges(busy_list, day_start_min=9*60, day_end_min=17*60):
    """
    busy_list: list of tuples (start_str, end_str) in 'HH:MM' format.
    Returns a set of (start_min, end_min) within work hours.
    """
    busy_blocks = set()
    for start_str, end_str in busy_list:
        s = time_to_minutes(datetime.strptime(start_str, "%H:%M"))
        e = time_to_minutes(datetime.strptime(end_str, "%H:%M"))
        # Clip to work hours
        s = max(s, day_start_min)
        e = min(e, day_end_min)
        if s < e:
            busy_blocks.add((s, e))
    return busy_blocks

def is_free(busy_blocks, slot_start, slot_end):
    """Check if slot [slot_start, slot_end] is free given busy blocks."""
    for bs, be in busy_blocks:
        if not (slot_end <= bs or slot_start >= be):
            return False
    return True

def find_slot(betty_busy, scott_busy, day_start_min=9*60, day_end_min=17*60, duration_min=30, betty_constraint=None):
    """
    betty_constraint: either None, or tuple (earliest_allowed_min) for that day.
    """
    # Generate all possible slot starts at :00 or :30 within work hours
    slot_starts = []
    t = day_start_min
    while t + duration_min <= day_end_min:
        slot_starts.append(t)
        t += 30
    
    for start_min in slot_starts:
        end_min = start_min + duration_min
        if betty_constraint is not None and start_min < betty_constraint:
            continue
        if is_free(betty_busy, start_min, end_min) and is_free(scott_busy, start_min, end_min):
            return start_min, end_min
    return None

def main():
    # Busy times for Betty
    betty_busy = {
        "Monday": [("10:00", "10:30"), ("13:30", "14:00"), ("15:00", "15:30"), ("16:00", "16:30")],
        "Tuesday": [("9:00", "9:30"), ("11:30", "12:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("16:30", "17:00")],
        "Wednesday": [("9:30", "10:30"), ("13:00", "13:30"), ("14:00", "14:30")],
        "Thursday": [("9:30", "10:00"), ("11:30", "12:00"), ("14:00", "14:30"), ("15:00", "15:30"), ("16:30", "17:00")]
    }
    
    # Busy times for Scott
    scott_busy = {
        "Monday": [("9:30", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")],
        "Tuesday": [("9:00", "9:30"), ("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "13:30"), ("14:00", "15:00"), ("16:00", "16:30")],
        "Wednesday": [("9:30", "12:30"), ("13:00", "13:30"), ("14:00", "14:30"), ("15:00", "15:30"), ("16:00", "16:30")],
        "Thursday": [("9:00", "9:30"), ("10:00", "10:30"), ("11:00", "12:00"), ("12:30", "13:00"), ("15:00", "16:00"), ("16:30", "17:00")]
    }
    
    # Betty's extra constraints
    betty_extra = {
        "Monday": None,  # None means cannot meet at all
        "Tuesday": 15 * 60,  # 15:00 in minutes
        "Wednesday": 9 * 60,  # 9:00, so anytime
        "Thursday": 15 * 60
    }
    
    # Order days respecting Scott's preference (avoid Wednesday if possible)
    days_to_try = ["Tuesday", "Thursday", "Wednesday"]  # Monday skipped due to Betty constraint
    
    work_start = 9 * 60
    work_end = 17 * 60
    duration = 30
    
    for day in days_to_try:
        if betty_extra[day] is None:
            continue
        betty_blocks = parse_busy_ranges(betty_busy[day], work_start, work_end)
        scott_blocks = parse_busy_ranges(scott_busy[day], work_start, work_end)
        
        slot = find_slot(betty_blocks, scott_blocks, work_start, work_end, duration, betty_extra[day])
        if slot:
            start_min, end_min = slot
            start_str = minutes_to_time_str(start_min)
            end_str = minutes_to_time_str(end_min)
            print(f"{day}:{start_str}:{end_str}")
            return
    
    print("No suitable slot found")

if __name__ == "__main__":
    main()