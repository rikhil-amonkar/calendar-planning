def time_to_minutes(t):
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    return f"{m // 60:02}:{m % 60:02}"

work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
duration = 30

participants = {
    "Emily": [
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:30"), time_to_minutes("12:30")),
        (time_to_minutes("14:00"), time_to_minutes("15:00")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ],
    "Melissa": [
        (time_to_minutes("09:30"), time_to_minutes("10:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00"))
    ],
    "Frank": [
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

for start in range(work_start, work_end - duration + 1, 15):
    end = start + duration
    if start >= time_to_minutes("09:30"):  # Frank's constraint
        continue
    
    conflict = False
    # Check Emily's schedule
    for s, e in participants["Emily"]:
        if not (end <= s or start >= e):
            conflict = True
            break
    if conflict:
        continue
    
    # Check Melissa's schedule
    for s, e in participants["Melissa"]:
        if not (end <= s or start >= e):
            conflict = True
            break
    if conflict:
        continue
    
    # Check Frank's schedule
    for s, e in participants["Frank"]:
        if not (end <= s or start >= e):
            conflict = True
            break
    if conflict:
        continue
    
    # Found valid slot
    print(f"Monday:{minutes_to_time(start)}:{minutes_to_time(end)}")
    exit()

# Fallback if no slot found (though problem states solution exists)
print("No valid slot found")