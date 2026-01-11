from datetime import datetime, timedelta

def parse_time(t_str):
    return datetime.strptime(t_str, "%H:%M")

def time_range(start, end):
    # returns list of minutes in the range
    s = parse_time(start)
    e = parse_time(end)
    delta = (e - s).seconds // 60
    return [(s + timedelta(minutes=m)).time() for m in range(delta)]

def busy_to_free(busy_slots, day_start, day_end, duration_minutes=30):
    day_start_t = parse_time(day_start).time()
    day_end_t = parse_time(day_end).time()
    
    # Convert busy slots to list of (start, end) as time objects
    busy_times = []
    for slot in busy_slots:
        s = parse_time(slot[0]).time()
        e = parse_time(slot[1]).time()
        busy_times.append((s, e))
    
    # Sort by start time
    busy_times.sort(key=lambda x: x[0])
    
    free_slots = []
    current = day_start_t
    
    for bs, be in busy_times:
        if current < bs:
            free_slots.append((current, bs))
        current = max(current, be)
    
    if current < day_end_t:
        free_slots.append((current, day_end_t))
    
    # Filter slots with enough duration
    valid_slots = []
    for fs, fe in free_slots:
        slot_minutes = (datetime.combine(datetime.today(), fe) - datetime.combine(datetime.today(), fs)).seconds // 60
        if slot_minutes >= duration_minutes:
            valid_slots.append((fs, fe))
    
    return valid_slots

def main():
    work_start = "09:00"
    work_end = "17:00"
    duration = 30
    
    # Jean's busy times (day-specific)
    jean_busy = {
        "Monday": [],
        "Tuesday": [("11:30", "12:00"), ("16:00", "16:30")]
    }
    
    # Doris's busy times
    doris_busy = {
        "Monday": [("09:00", "11:30"), ("12:00", "12:30"), ("13:30", "16:00"), ("16:30", "17:00")],
        "Tuesday": [("09:00", "17:00")]
    }
    
    days = ["Monday", "Tuesday"]
    
    for day in days:
        # Get free slots for each person
        jean_free = busy_to_free(jean_busy[day], work_start, work_end, duration)
        doris_free = busy_to_free(doris_busy[day], work_start, work_end, duration)
        
        # Find overlapping free slots
        for js, je in jean_free:
            for ds, de in doris_free:
                overlap_start = max(js, ds)
                overlap_end = min(je, de)
                overlap_minutes = (datetime.combine(datetime.today(), overlap_end) - 
                                   datetime.combine(datetime.today(), overlap_start)).seconds // 60
                if overlap_minutes >= duration:
                    # Found a slot
                    # Apply Doris's preference: avoid Monday after 14:00
                    if day == "Monday" and overlap_start >= parse_time("14:00").time():
                        continue  # skip, she'd rather not
                    # Choose earliest start in this overlap
                    meeting_start = overlap_start
                    meeting_end = (datetime.combine(datetime.today(), meeting_start) + timedelta(minutes=duration)).time()
                    print(f"{day}")
                    print(f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}")
                    return
    
    print("No suitable time found.")

if __name__ == "__main__":
    main()