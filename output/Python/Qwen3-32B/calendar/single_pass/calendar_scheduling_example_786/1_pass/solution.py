import datetime

def is_slot_free(slot_start, slot_end, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        if slot_start < busy_end and busy_start < slot_end:
            return False
    return True

def generate_slots():
    days = ['Monday', 'Tuesday', 'Wednesday']
    amy_busy = {
        'Monday': [],
        'Tuesday': [],
        'Wednesday': [
            (datetime.time(11, 0), datetime.time(11, 30)),
            (datetime.time(13, 30), datetime.time(14, 0)),
        ],
    }
    pamela_busy = {
        'Monday': [
            (datetime.time(9, 0), datetime.time(10, 30)),
            (datetime.time(11, 0), datetime.time(16, 30)),
        ],
        'Tuesday': [
            (datetime.time(9, 0), datetime.time(9, 30)),
            (datetime.time(10, 0), datetime.time(17, 0)),
        ],
        'Wednesday': [
            (datetime.time(9, 0), datetime.time(9, 30)),
            (datetime.time(10, 0), datetime.time(11, 0)),
            (datetime.time(11, 30), datetime.time(13, 30)),
            (datetime.time(14, 30), datetime.time(15, 0)),
            (datetime.time(16, 0), datetime.time(16, 30)),
        ],
    }
    valid_slots = []
    for day in days:
        for start_minutes in range(9*60, 17*60, 30):
            if start_minutes + 30 > 17*60:
                continue
            start_hour = start_minutes // 60
            start_minute = start_minutes % 60
            start_time = datetime.time(start_hour, start_minute)
            end_time = (datetime.datetime.combine(datetime.date.today(), start_time) + datetime.timedelta(minutes=30)).time()
            amy_intervals = amy_busy.get(day, [])
            pamela_intervals = pamela_busy.get(day, [])
            amy_free = is_slot_free(start_time, end_time, amy_intervals)
            pamela_free = is_slot_free(start_time, end_time, pamela_intervals)
            if amy_free and pamela_free:
                valid_slots.append( (day, start_time, end_time) )
    def get_priority(slot):
        day, start, end = slot
        if day == 'Wednesday':
            if start >= datetime.time(16, 0):
                return 0
            else:
                return 2
        elif day == 'Tuesday':
            if start >= datetime.time(16, 0):
                return 1
            else:
                return 3
        elif day == 'Monday':
            return 4
        else:
            return 5
    valid_slots.sort(key=get_priority)
    if valid_slots:
        best_slot = valid_slots[0]
        day, start, end = best_slot
        start_str = start.strftime("%H:%M")
        end_str = end.strftime("%H:%M")
        time_range = f"{start_str}:{end_str}"
        return time_range, day
    else:
        return None, None

time_range, day = generate_slots()
print(f"{time_range} {day}")