from datetime import time, timedelta

def time_to_minutes(t):
    return t.hour * 60 + t.minute

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return time(hours, minutes)

def busy_range_to_minutes(busy_list):
    # busy_list: list of tuples (day, start_time, end_time)
    busy_minutes = {day: [] for day in ['Monday', 'Tuesday', 'Wednesday']}
    for day, start_str, end_str in busy_list:
        start_t = time.fromisoformat(start_str)
        end_t = time.fromisoformat(end_str)
        busy_minutes[day].append((time_to_minutes(start_t), time_to_minutes(end_t)))
    return busy_minutes

def is_free(person_busy, day, start_min, end_min):
    for busy_start, busy_end in person_busy[day]:
        if not (end_min <= busy_start or start_min >= busy_end):
            return False
    return True

def main():
    # Busy times in (day, "HH:MM", "HH:MM") format
    tyler_busy = [
        ('Tuesday', '09:00', '09:30'),
        ('Tuesday', '14:30', '15:00'),
        ('Wednesday', '10:30', '11:00'),
        ('Wednesday', '12:30', '13:00'),
        ('Wednesday', '13:30', '14:00'),
        ('Wednesday', '16:30', '17:00'),
    ]
    
    ruth_busy = [
        ('Monday', '09:00', '10:00'),
        ('Monday', '10:30', '12:00'),
        ('Monday', '12:30', '14:30'),
        ('Monday', '15:00', '16:00'),
        ('Monday', '16:30', '17:00'),
        ('Tuesday', '09:00', '17:00'),
        ('Wednesday', '09:00', '17:00'),
    ]
    
    tyler_busy_min = busy_range_to_minutes(tyler_busy)
    ruth_busy_min = busy_range_to_minutes(ruth_busy)
    
    days = ['Monday', 'Tuesday', 'Wednesday']
    work_start = time_to_minutes(time(9, 0))
    work_end = time_to_minutes(time(17, 0))
    meeting_duration = 30
    
    possible_slots = []
    
    for day in days:
        for start_min in range(work_start, work_end - meeting_duration + 1, 15):  # check every 15 minutes for flexibility
            end_min = start_min + meeting_duration
            if (is_free(tyler_busy_min, day, start_min, end_min) and
                is_free(ruth_busy_min, day, start_min, end_min)):
                # Tyler's preference: avoid Monday before 16:00
                if day == 'Monday' and end_min <= time_to_minutes(time(16, 0)):
                    continue
                possible_slots.append((day, start_min, end_min))
    
    # Pick the first possible slot
    if possible_slots:
        day, start_min, end_min = possible_slots[0]
        start_time = minutes_to_time(start_min).strftime('%H:%M')
        end_time = minutes_to_time(end_min).strftime('%H:%M')
        print(f"{day}:{start_time}:{end_time}")
    else:
        print("No suitable slot found")

if __name__ == '__main__':
    main()