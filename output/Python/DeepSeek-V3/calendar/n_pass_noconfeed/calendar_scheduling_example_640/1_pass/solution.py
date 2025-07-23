from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M").time()

def time_to_minutes(time_obj):
    return time_obj.hour * 60 + time_obj.minute

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return datetime.strptime(f"{hours:02d}:{minutes:02d}", "%H:%M").time()

def get_available_slots(busy_slots, day_start, day_end, duration):
    day_start_min = time_to_minutes(day_start)
    day_end_min = time_to_minutes(day_end)
    busy_slots_min = [(time_to_minutes(start), time_to_minutes(end)) for start, end in busy_slots]
    busy_slots_min.sort()
    
    available_slots = []
    prev_end = day_start_min
    
    for start, end in busy_slots_min:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < day_end_min:
        available_slots.append((prev_end, day_end_min))
    
    valid_slots = []
    for start, end in available_slots:
        if end - start >= duration:
            valid_slots.append((start, end))
    
    return valid_slots

def find_earliest_meeting_time(participants_schedules, days, duration_minutes):
    day_start = parse_time("09:00")
    day_end = parse_time("17:00")
    
    for day in days:
        all_participants_slots = []
        for participant in participants_schedules:
            busy_slots = participants_schedules[participant][day]
            available_slots = get_available_slots(busy_slots, day_start, day_end, duration_minutes)
            all_participants_slots.append(available_slots)
        
        common_slots = []
        if all_participants_slots:
            common_slots = all_participants_slots[0]
            for slots in all_participants_slots[1:]:
                new_common_slots = []
                i = j = 0
                while i < len(common_slots) and j < len(slots):
                    start1, end1 = common_slots[i]
                    start2, end2 = slots[j]
                    
                    overlap_start = max(start1, start2)
                    overlap_end = min(end1, end2)
                    
                    if overlap_start < overlap_end:
                        new_common_slots.append((overlap_start, overlap_end))
                    
                    if end1 < end2:
                        i += 1
                    else:
                        j += 1
                common_slots = new_common_slots
        
        if common_slots:
            earliest_slot = common_slots[0]
            start_time = minutes_to_time(earliest_slot[0])
            end_time = minutes_to_time(earliest_slot[0] + duration_minutes)
            return day, start_time, end_time
    
    return None, None, None

def main():
    participants_schedules = {
        "Bobby": {
            "Monday": [(parse_time("14:30"), parse_time("15:00"))],
            "Tuesday": [
                (parse_time("09:00"), parse_time("11:30")),
                (parse_time("12:00"), parse_time("12:30")),
                (parse_time("13:00"), parse_time("15:00")),
                (parse_time("15:30"), parse_time("17:00"))
            ]
        },
        "Michael": {
            "Monday": [
                (parse_time("09:00"), parse_time("10:00")),
                (parse_time("10:30"), parse_time("13:30")),
                (parse_time("14:00"), parse_time("15:00")),
                (parse_time("15:30"), parse_time("17:00"))
            ],
            "Tuesday": [
                (parse_time("09:00"), parse_time("10:30")),
                (parse_time("11:00"), parse_time("11:30")),
                (parse_time("12:00"), parse_time("14:00")),
                (parse_time("15:00"), parse_time("16:00")),
                (parse_time("16:30"), parse_time("17:00"))
            ]
        }
    }
    
    days = ["Monday", "Tuesday"]
    duration_minutes = 30
    
    day, start_time, end_time = find_earliest_meeting_time(participants_schedules, days, duration_minutes)
    
    if day and start_time and end_time:
        print(f"{day}: {start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}")
    else:
        print("No available time slot found.")

if __name__ == "__main__":
    main()