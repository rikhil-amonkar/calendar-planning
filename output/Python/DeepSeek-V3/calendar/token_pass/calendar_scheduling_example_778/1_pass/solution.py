from datetime import datetime, timedelta

def parse_time(t_str):
    return datetime.strptime(t_str, "%H:%M")

def time_range(start, end):
    # yields every 30-minute slot within start to end
    current = start
    while current + timedelta(minutes=30) <= end:
        yield (current, current + timedelta(minutes=30))
        current += timedelta(minutes=30)

def blocked_to_free(blocked, day_start, day_end):
    # blocked: list of (start, end)
    # sort blocked times
    blocked = sorted(blocked, key=lambda x: x[0])
    free = []
    current = day_start
    for (b_start, b_end) in blocked:
        if current < b_start:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < day_end:
        free.append((current, day_end))
    return free

def main():
    day_start = parse_time("09:00")
    day_end = parse_time("17:00")
    duration = timedelta(minutes=30)
    
    # Susan's blocked times per day
    susan_blocked = {
        "Monday": [("12:30", "13:00"), ("13:30", "14:00")],
        "Tuesday": [("11:30", "12:00")],
        "Wednesday": [("9:30", "10:30"), ("14:00", "14:30"), ("15:30", "16:30")],
    }
    
    # Sandra's blocked times per day
    sandra_blocked = {
        "Monday": [("9:00", "13:00"), ("14:00", "15:00"), ("16:00", "16:30")],
        "Tuesday": [("9:00", "9:30"), ("10:30", "12:00"), ("12:30", "13:30"), ("14:00", "14:30"), ("16:00", "17:00")],
        "Wednesday": [("9:00", "11:30"), ("12:00", "12:30"), ("13:00", "17:00")],
    }
    
    days = ["Monday", "Tuesday", "Wednesday"]
    
    # Find all free slots
    possible_slots = []
    
    for day in days:
        # Convert blocked times to datetime objects
        susan_b = [(parse_time(s), parse_time(e)) for s, e in susan_blocked.get(day, [])]
        sandra_b = [(parse_time(s), parse_time(e)) for s, e in sandra_blocked.get(day, [])]
        
        susan_free = blocked_to_free(susan_b, day_start, day_end)
        sandra_free = blocked_to_free(sandra_b, day_start, day_end)
        
        # Find overlapping free periods
        for fs, fe in susan_free:
            for ss, se in sandra_free:
                overlap_start = max(fs, ss)
                overlap_end = min(fe, se)
                if overlap_start + duration <= overlap_end:
                    # Generate 30-minute slots within this overlap
                    slot_start = overlap_start
                    while slot_start + duration <= overlap_end:
                        possible_slots.append((day, slot_start, slot_start + duration))
                        slot_start += timedelta(minutes=30)
    
    # Sort slots by day order and time
    day_order = {day: i for i, day in enumerate(days)}
    possible_slots.sort(key=lambda x: (day_order[x[0]], x[1]))
    
    # Pick first non-Tuesday slot (Susan's preference)
    chosen = None
    for slot in possible_slots:
        if slot[0] != "Tuesday":
            chosen = slot
            break
    
    # If all are Tuesday, pick first Tuesday slot
    if chosen is None and possible_slots:
        chosen = possible_slots[0]
    
    if chosen:
        day, start, end = chosen
        print(f"{day}")
        print(f"{start.strftime('%H:%M')}:{end.strftime('%H:%M')}")
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()