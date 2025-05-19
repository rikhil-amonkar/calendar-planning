def time_to_min(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

participants = {
    'Olivia': [(time_to_min('12:30'), time_to_min('13:30')), 
               (time_to_min('14:30'), time_to_min('15:00')), 
               (time_to_min('16:30'), time_to_min('17:00'))],
    'Virginia': [(time_to_min('9:00'), time_to_min('10:00')), 
                 (time_to_min('11:30'), time_to_min('16:00')), 
                 (time_to_min('16:30'), time_to_min('17:00'))],
    'Paul': [(time_to_min('9:00'), time_to_min('9:30')), 
             (time_to_min('11:00'), time_to_min('11:30')), 
             (time_to_min('13:00'), time_to_min('14:00')), 
             (time_to_min('14:30'), time_to_min('16:00')), 
             (time_to_min('16:30'), time_to_min('17:00'))]
}

work_start = time_to_min('09:00')
work_end = time_to_min('17:00')
duration = 60

for start in range(work_start, work_end - duration + 1):
    end = start + duration
    valid = True
    for person, blocks in participants.items():
        for s, e in blocks:
            if not (end <= s or start >= e):
                valid = False
                break
        if not valid:
            break
    if valid:
        print(f"{min_to_time(start)}-{min_to_time(end)}")
        print("Monday")
        exit()

print("No suitable time found")