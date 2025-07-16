def time_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

ronald_blocks = {
    'Monday': [('10:30', '11:00'), ('12:00', '12:30'), ('15:30', '16:00')],
    'Tuesday': [('9:00', '9:30'), ('12:00', '12:30'), ('15:30', '16:30')],
    'Wednesday': [('9:30', '10:30'), ('11:00', '12:00'), ('12:30', '13:00'), ('13:30', '14:00'), ('16:30', '17:00')]
}

amber_blocks = {
    'Monday': [('9:00', '9:30'), ('10:00', '10:30'), ('11:30', '12:00'), ('12:30', '14:00'), ('14:30', '15:00'), ('15:30', '17:00')],
    'Tuesday': [('9:00', '9:30'), ('10:00', '11:30'), ('12:00', '12:30'), ('13:30', '15:30'), ('16:30', '17:00')],
    'Wednesday': [('9:00', '9:30'), ('10:00', '10:30'), ('11:00', '13:30'), ('15:00', '15:30')]
}

work_start = "9:00"
work_end = "17:00"
days = ['Monday', 'Tuesday', 'Wednesday']

work_start_min = time_to_minutes(work_start)
work_end_min = time_to_minutes(work_end)

for day in days:
    current = work_start_min
    while current < work_end_min:
        slot_end = current + 30
        if slot_end > work_end_min:
            break
            
        # Check Ronald's blocks for the day
        r_blocked = False
        if day in ronald_blocks:
            for block in ronald_blocks[day]:
                b_start = time_to_minutes(block[0])
                b_end = time_to_minutes(block[1])
                if not (slot_end <= b_start or current >= b_end):
                    r_blocked = True
                    break
                    
        if r_blocked:
            current += 30
            continue
            
        # Check Amber's blocks for the day
        a_blocked = False
        if day in amber_blocks:
            for block in amber_blocks[day]:
                b_start = time_to_minutes(block[0])
                b_end = time_to_minutes(block[1])
                if not (slot_end <= b_start or current >= b_end):
                    a_blocked = True
                    break
                    
        if not a_blocked:
            start_time_str = minutes_to_time(current)
            end_time_str = minutes_to_time(slot_end)
            s_h, s_m = start_time_str.split(':')
            e_h, e_m = end_time_str.split(':')
            time_range_str = f"{s_h}:{s_m}:{e_h}:{e_m}"
            print(day)
            print(time_range_str)
            exit(0)
            
        current += 30

print("No slot found")
exit(1)