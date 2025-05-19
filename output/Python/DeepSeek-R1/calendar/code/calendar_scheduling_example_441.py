def time_to_minutes(t):
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

participants = {
    "Joan": [("11:30", "12:00"), ("14:30", "15:00")],
    "Megan": [("9:00", "10:00"), ("14:00", "14:30"), ("16:00", "16:30")],
    "Austin": [],
    "Betty": [("9:30", "10:00"), ("11:30", "12:00"), ("13:30", "14:00"), ("16:00", "16:30")],
    "Judith": [("9:00", "11:00"), ("12:00", "13:00"), ("14:00", "15:00")],
    "Terry": [("9:30", "10:00"), ("11:30", "12:30"), ("13:00", "14:00"), ("15:00", "15:30"), ("16:00", "17:00")],
    "Kathryn": [("9:30", "10:00"), ("10:30", "11:00"), ("11:30", "13:00"), ("14:00", "16:00"), ("16:30", "17:00")]
}

work_start = time_to_minutes("9:00")
work_end = time_to_minutes("17:00")
duration = 30

for start in range(work_start, work_end - duration + 1, 15):
    end = start + duration
    slot_ok = True
    for person, meetings in participants.items():
        for meet_start, meet_end in meetings:
            meet_start_m = time_to_minutes(meet_start)
            meet_end_m = time_to_minutes(meet_end)
            if not (end <= meet_start_m or start >= meet_end_m):
                slot_ok = False
                break
        if not slot_ok:
            break
    if slot_ok:
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(end)
        print(f"Monday {start_time}:{end_time}")
        exit()

print("No suitable time found")