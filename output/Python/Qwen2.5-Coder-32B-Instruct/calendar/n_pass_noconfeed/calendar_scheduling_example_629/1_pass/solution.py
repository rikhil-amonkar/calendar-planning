from datetime import datetime, timedelta

def find_meeting_time(margaret_schedule, alexis_schedule, meeting_duration, preferred_day, preferred_start_time):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    def parse_schedule(schedule):
        return [tuple(map(lambda x: datetime.strptime(x, "%H:%M"), slot.split(" to "))) for slot in schedule]
    
    margaret_slots = parse_schedule(margaret_schedule)
    alexis_slots = parse_schedule(alexis_schedule)
    
    def available_slots(slots, start=work_start, end=work_end):
        slots.sort()
        free_slots = []
        current_start = start
        
        for slot in slots:
            if current_start < slot[0]:
                free_slots.append((current_start, slot[0]))
            current_start = max(current_start, slot[1])
        
        if current_start < end:
            free_slots.append((current_start, end))
        
        return free_slots
    
    margaret_free = available_slots(margaret_slots)
    alexis_free = available_slots(alexis_slots)
    
    def find_common_slot(day_slots1, day_slots2, duration):
        for slot1 in day_slots1:
            for slot2 in day_slots2:
                common_start = max(slot1[0], slot2[0])
                common_end = min(slot1[1], slot2[1])
                if (common_end - common_start) >= timedelta(minutes=duration):
                    return common_start, common_start + timedelta(minutes=duration)
        return None, None
    
    meeting_start, meeting_end = find_common_slot(margaret_free, alexis_free, meeting_duration)
    
    if meeting_start and meeting_end:
        return f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}", preferred_day
    else:
        return None, None

margaret_schedule = ["10:30 to 11:00", "11:30 to 12:00", "13:00 to 13:30", "15:00 to 17:00"]
alexis_schedule = ["9:30 to 11:30", "12:30 to 13:00", "14:00 to 17:00"]
meeting_duration = 30
preferred_day = "Tuesday"
preferred_start_time = datetime.strptime("14:30", "%H:%M")

meeting_time, meeting_day = find_meeting_time(margaret_schedule, alexis_schedule, meeting_duration, preferred_day, preferred_start_time)

if meeting_time and meeting_day:
    print(f"{meeting_time} {meeting_day}")
else:
    print("No suitable time found.")