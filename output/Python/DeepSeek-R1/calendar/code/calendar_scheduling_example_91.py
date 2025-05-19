def time_to_minutes(time):
    hours, minutes = map(int, time.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
duration = 60

busy = {
    "Danielle": [(540, 600), (630, 660), (870, 900), (930, 960), (990, 1020)],
    "Bruce": [(660, 690), (750, 780), (840, 870), (930, 960)],
    "Eric": [(540, 570), (600, 660), (690, 780), (870, 930)]
}

for start in range(work_start, work_end - duration + 1):
    end = start + duration
    if end > work_end:
        continue
    all_free = True
    for person in busy:
        for (s, e) in busy[person]:
            if not (end <= s or start >= e):
                all_free = False
                break
        if not all_free:
            break
    if all_free:
        print(f"{minutes_to_time(start)}-{minutes_to_time(end)}")
        print("Monday")
        exit()

print("No suitable time found")