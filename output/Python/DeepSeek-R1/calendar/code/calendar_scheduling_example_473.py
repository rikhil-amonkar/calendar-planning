def time_to_minutes(t):
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

participants = [
    {  # Gregory
        'busy': [(time_to_minutes('09:00'), time_to_minutes('09:30')),
                 (time_to_minutes('11:30'), time_to_minutes('12:00'))]
    },
    {  # Jonathan
        'busy': [(time_to_minutes('09:00'), time_to_minutes('09:30')),
                 (time_to_minutes('12:00'), time_to_minutes('12:30')),
                 (time_to_minutes('13:00'), time_to_minutes('13:30')),
                 (time_to_minutes('15:00'), time_to_minutes('16:00')),
                 (time_to_minutes('16:30'), time_to_minutes('17:00'))]
    },
    {  # Barbara
        'busy': [(time_to_minutes('10:00'), time_to_minutes('10:30')),
                 (time_to_minutes('13:30'), time_to_minutes('14:00'))]
    },
    {  # Jesse
        'busy': [(time_to_minutes('10:00'), time_to_minutes('11:00')),
                 (time_to_minutes('12:30'), time_to_minutes('14:30'))]
    },
    {  # Alan
        'busy': [(time_to_minutes('09:30'), time_to_minutes('11:00')),
                 (time_to_minutes('11:30'), time_to_minutes('12:30')),
                 (time_to_minutes('13:00'), time_to_minutes('15:30')),
                 (time_to_minutes('16:00'), time_to_minutes('17:00'))]
    },
    {  # Nicole
        'busy': [(time_to_minutes('09:00'), time_to_minutes('10:30')),
                 (time_to_minutes('11:30'), time_to_minutes('12:00')),
                 (time_to_minutes('12:30'), time_to_minutes('13:30')),
                 (time_to_minutes('14:00'), time_to_minutes('17:00'))]
    },
    {  # Catherine
        'busy': [(time_to_minutes('09:00'), time_to_minutes('10:30')),
                 (time_to_minutes('12:00'), time_to_minutes('13:30')),
                 (time_to_minutes('15:00'), time_to_minutes('15:30')),
                 (time_to_minutes('16:00'), time_to_minutes('16:30'))]
    }
]

start_work = time_to_minutes('09:00')
end_work = time_to_minutes('17:00')
duration = 30

for start in range(start_work, end_work - duration + 1):
    end = start + duration
    all_available = True
    for participant in participants:
        busy = False
        for (busy_start, busy_end) in participant['busy']:
            if start < busy_end and end > busy_start:
                busy = True
                break
        if busy:
            all_available = False
            break
    if all_available:
        print(f"Monday {minutes_to_time(start)}:{minutes_to_time(end)}")
        exit()

print("No suitable time found")