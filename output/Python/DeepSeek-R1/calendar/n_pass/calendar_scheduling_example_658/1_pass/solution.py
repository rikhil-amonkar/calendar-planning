def time_str_to_minutes(time_str):
    hours, minutes = time_str.split(':')
    return int(hours) * 60 + int(minutes)

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_slots(work_start, work_end, busy_list):
    free_slots = [(work_start, work_end)]
    if not busy_list:
        return free_slots
    
    busy_intervals = []
    for busy in busy_list:
        s = time_str_to_minutes(busy[0])
        e = time_str_to_minutes(busy[1])
        busy_intervals.append((s, e))
    busy_intervals.sort(key=lambda x: x[0])
    
    for busy in busy_intervals:
        new_free = []
        for slot in free_slots:
            if slot[1] <= busy[0] or slot[0] >= busy[1]:
                new_free.append(slot)
            else:
                if slot[0] < busy[0]:
                    new_free.append((slot[0], busy[0]))
                if slot[1] > busy[1]:
                    new_free.append((busy[1], slot[1]))
        free_slots = new_free
    return free_slots

def find_common_slots(slots1, slots2, duration):
    common = []
    for slot1 in slots1:
        for slot2 in slots2:
            start_overlap = max(slot1[0], slot2[0])
            end_overlap = min(slot1[1], slot2[1])
            if start_overlap < end_overlap and (end_overlap - start_overlap) >= duration:
                common.append((start_overlap, end_overlap))
    common.sort(key=lambda x: x[0])
    return common

def main():
    work_start = time_str_to_minutes('09:00')
    work_end = time_str_to_minutes('17:00')
    duration = 30
    
    shirley_busy = {
        'Monday': [('10:30','11:00'), ('12:00','12:30'), ('16:00','16:30')],
        'Tuesday': [('09:30','10:00')]
    }
    
    albert_busy = {
        'Monday': [('09:00','17:00')],
        'Tuesday': [('09:30','11:00'), ('11:30','12:30'), ('13:00','16:00'), ('16:30','17:00')]
    }
    
    days = ['Monday', 'Tuesday']
    tuesday_cutoff = time_str_to_minutes('10:30')
    
    for day in days:
        shirley_free = get_free_slots(work_start, work_end, shirley_busy.get(day, []))
        albert_free = get_free_slots(work_start, work_end, albert_busy.get(day, []))
        common = find_common_slots(shirley_free, albert_free, duration)
        
        if day == 'Tuesday':
            common = [slot for slot in common if slot[0] < tuesday_cutoff]
            
        if common:
            slot = common[0]
            start_minutes = slot[0]
            end_minutes = start_minutes + duration
            start_str = minutes_to_time(start_minutes)
            end_str = minutes_to_time(end_minutes)
            print(day)
            print(f"{start_str}:{end_str}")
            return

if __name__ == '__main__':
    main()