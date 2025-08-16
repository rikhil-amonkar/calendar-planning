from datetime import datetime, timedelta

def find_meeting_time(jean_schedule, doris_schedule, preferred_day, preferred_end_time):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    meeting_duration = timedelta(minutes=30)
    
    def parse_schedule(schedule):
        return [tuple(datetime.strptime(time, "%H:%M") for time in slot.split(" to ")) for slot in schedule]
    
    jean_slots = parse_schedule(jean_schedule)
    doris_slots = parse_schedule(doris_schedule)
    
    def is_free(slots, start, end):
        for slot in slots:
            if start < slot[1] and end > slot[0]:
                return False
        return True
    
    for day in ['Monday', 'Tuesday']:
        current_time = work_start
        while current_time + meeting_duration <= work_end:
            next_time = current_time + meeting_duration
            if (day == preferred_day or current_time < preferred_end_time) and \
               is_free(jean_slots, current_time, next_time) and \
               is_free(doris_slots, current_time, next_time):
                return f"{current_time.strftime('%H:%M')}:{next_time.strftime('%H:%M')}", day
            current_time += timedelta(minutes=15)
    
    return None, None

jean_schedule = ["11:30 to 12:00", "16:00 to 16:30"]
doris_schedule = ["9:00 to 11:30", "12:00 to 12:30", "13:30 to 16:00", "16:30 to 17:00"]
preferred_day = 'Monday'
preferred_end_time = datetime.strptime("14:00", "%H:%M")

meeting_time, meeting_day = find_meeting_time(jean_schedule, doris_schedule, preferred_day, preferred_end_time)
print(f"{meeting_time}:{meeting_day}")