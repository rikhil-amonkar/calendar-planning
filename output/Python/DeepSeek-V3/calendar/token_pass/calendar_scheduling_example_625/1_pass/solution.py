from datetime import datetime, timedelta

def parse_time(t_str):
    return datetime.strptime(t_str, "%H:%M")

def time_to_str(t):
    return t.strftime("%H:%M")

def find_meeting_slot(busy_slots, work_start, work_end, duration_minutes, preferences):
    """
    busy_slots: list of (day, start, end) for each busy block
    work_start, work_end: time objects
    duration: minutes
    preferences: dict with 'avoid_day' and 'avoid_before' (time)
    returns: (day, start_time, end_time) or None
    """
    duration = timedelta(minutes=duration_minutes)
    days = ["Monday", "Tuesday"]
    
    # Convert work hours to datetime for calculation (using arbitrary date)
    base_date = datetime(2023, 1, 1)
    work_start_dt = datetime.combine(base_date.date(), work_start)
    work_end_dt = datetime.combine(base_date.date(), work_end)
    
    # Generate slots for each day
    possible_slots = []
    for day in days:
        # Start with whole work period free
        free_start = work_start_dt
        # Get busy slots for this day
        day_busy = [(s, e) for d, s, e in busy_slots if d == day]
        # Sort by start time
        day_busy.sort(key=lambda x: x[0])
        
        # Find free intervals
        for busy_start, busy_end in day_busy:
            if free_start < busy_start:
                # Free slot from free_start to busy_start
                if busy_start - free_start >= duration:
                    possible_slots.append((day, free_start.time(), busy_start.time()))
            # Move free_start to end of this busy period
            if busy_end > free_start:
                free_start = busy_end
        # After last busy slot
        if free_start < work_end_dt:
            if work_end_dt - free_start >= duration:
                possible_slots.append((day, free_start.time(), work_end_dt.time()))
    
    # Apply preferences
    def slot_score(slot):
        day, start_t, _ = slot
        score = 0
        # Prefer slots not on avoid_day
        if preferences.get('avoid_day') == day:
            score += 10  # higher score = worse
        # Prefer slots not before avoid_before
        avoid_before = preferences.get('avoid_before')
        if avoid_before and start_t < avoid_before:
            score += 5
        return score
    
    if not possible_slots:
        return None
    
    # Sort by score then by day and time
    possible_slots.sort(key=lambda x: (slot_score(x), x[0], x[1]))
    
    # Pick first slot, adjust end time to start + duration
    best_day, start_time, _ = possible_slots[0]
    start_dt = datetime.combine(base_date.date(), start_time)
    end_dt = start_dt + duration
    return best_day, start_dt.time(), end_dt.time()

def main():
    # Define work hours
    work_start = parse_time("09:00").time()
    work_end = parse_time("17:00").time()
    
    # Harold's busy times (day, start, end) as datetime.time
    busy = [
        ("Monday", parse_time("09:00").time(), parse_time("10:00").time()),
        ("Monday", parse_time("10:30").time(), parse_time("17:00").time()),
        ("Tuesday", parse_time("09:00").time(), parse_time("09:30").time()),
        ("Tuesday", parse_time("10:30").time(), parse_time("11:30").time()),
        ("Tuesday", parse_time("12:30").time(), parse_time("13:30").time()),
        ("Tuesday", parse_time("14:30").time(), parse_time("15:30").time()),
        ("Tuesday", parse_time("16:00").time(), parse_time("17:00").time()),
    ]
    
    # Preferences
    preferences = {
        'avoid_day': 'Monday',
        'avoid_before': parse_time("14:30").time()
    }
    
    result = find_meeting_slot(busy, work_start, work_end, 30, preferences)
    
    if result:
        day, start_t, end_t = result
        print(f"{day}")
        print(f"{start_t.strftime('%H:%M')}:{end_t.strftime('%H:%M')}")
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()