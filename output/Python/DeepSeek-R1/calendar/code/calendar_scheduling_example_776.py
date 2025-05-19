import datetime

def find_meeting_time():
    possible_days = ['Monday', 'Tuesday', 'Wednesday']
    meeting_duration = datetime.timedelta(minutes=30)
    work_start = datetime.time(9, 0)
    work_end = datetime.time(17, 0)

    jennifer_busy = {
        'Monday': [
            (datetime.time(9, 0), datetime.time(11, 0)),
            (datetime.time(11, 30), datetime.time(13, 0)),
            (datetime.time(13, 30), datetime.time(14, 30)),
            (datetime.time(15, 0), datetime.time(17, 0))
        ],
        'Tuesday': [
            (datetime.time(9, 0), datetime.time(11, 30)),
            (datetime.time(12, 0), datetime.time(17, 0))
        ],
        'Wednesday': [
            (datetime.time(9, 0), datetime.time(11, 30)),
            (datetime.time(12, 0), datetime.time(12, 30)),
            (datetime.time(13, 0), datetime.time(14, 0)),
            (datetime.time(14, 30), datetime.time(16, 0)),
            (datetime.time(16, 30), datetime.time(17, 0))
        ]
    }

    john_unavailable_days = ['Tuesday', 'Wednesday']
    john_avoid_monday_after = datetime.time(14, 30)

    for day in possible_days:
        if day in john_unavailable_days:
            continue

        busy = jennifer_busy.get(day, [])
        free_slots = []

        current_start = work_start
        for interval in busy:
            if current_start < interval[0]:
                free_slots.append((current_start, interval[0]))
            current_start = interval[1]
        if current_start < work_end:
            free_slots.append((current_start, work_end))

        for slot_start, slot_end in free_slots:
            if day == 'Monday':
                latest_end = datetime.datetime.combine(datetime.date.today(), john_avoid_monday_after)
                slot_end_time = datetime.datetime.combine(datetime.date.today(), slot_end)
                if slot_end_time > latest_end:
                    slot_end = john_avoid_monday_after

            slot_duration = datetime.datetime.combine(datetime.date.today(), slot_end) - datetime.datetime.combine(datetime.date.today(), slot_start)
            if slot_duration >= meeting_duration:
                meeting_end = (datetime.datetime.combine(datetime.date.today(), slot_start) + meeting_duration).time()
                if day == 'Monday' and meeting_end > john_avoid_monday_after:
                    continue
                return (day, slot_start.strftime("%H:%M"), meeting_end.strftime("%H:%M"))

    return None

result = find_meeting_time()
if result:
    day, start, end = result
    print(f"{day} {start}:{end}")
else:
    print("No suitable time found")