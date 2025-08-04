from datetime import datetime, timedelta

def find_meeting_time(bobby_schedule, michael_schedule, meeting_duration, work_start, work_end, days):
    meeting_duration = timedelta(hours=meeting_duration)
    work_start = datetime.strptime(work_start, "%H:%M")
    work_end = datetime.strptime(work_end, "%H:%M")

    for day in days:
        bobby_busy = bobby_schedule[day]
        michael_busy = michael_schedule[day]

        bobby_free = []
        michael_free = []

        current_time = work_start
        while current_time < work_end:
            next_bobby_busy = next((busy for busy in bobby_busy if busy['start'] > current_time), {'start': work_end})
            next_michael_busy = next((busy for busy in michael_busy if busy['start'] > current_time), {'start': work_end})

            bobby_free.append({'start': current_time, 'end': next_bobby_busy['start']})
            michael_free.append({'start': current_time, 'end': next_michael_busy['start']})

            current_time = max(next_bobby_busy['start'], next_michael_busy['start'])

        for bobby_slot in bobby_free:
            for michael_slot in michael_free:
                start_time = max(bobby_slot['start'], michael_slot['start'])
                end_time = min(bobby_slot['end'], michael_slot['end'])

                if end_time - start_time >= meeting_duration:
                    return f"{start_time.strftime('%H:%M')}:{(start_time + meeting_duration).strftime('%H:%M')}", day

    return None, None

bobby_schedule = {
    "Monday": [{'start': datetime.strptime("14:30", "%H:%M"), 'end': datetime.strptime("15:00", "%H:%M")}],
    "Tuesday": [
        {'start': datetime.strptime("9:00", "%H:%M"), 'end': datetime.strptime("11:30", "%H:%M")},
        {'start': datetime.strptime("12:00", "%H:%M"), 'end': datetime.strptime("12:30", "%H:%M")},
        {'start': datetime.strptime("13:00", "%H:%M"), 'end': datetime.strptime("15:00", "%H:%M")},
        {'start': datetime.strptime("15:30", "%H:%M"), 'end': datetime.strptime("17:00", "%H:%M")}
    ]
}

michael_schedule = {
    "Monday": [
        {'start': datetime.strptime("9:00", "%H:%M"), 'end': datetime.strptime("10:00", "%H:%M")},
        {'start': datetime.strptime("10:30", "%H:%M"), 'end': datetime.strptime("13:30", "%H:%M")},
        {'start': datetime.strptime("14:00", "%H:%M"), 'end': datetime.strptime("15:00", "%H:%M")},
        {'start': datetime.strptime("15:30", "%H:%M"), 'end': datetime.strptime("17:00", "%H:%M")}
    ],
    "Tuesday": [
        {'start': datetime.strptime("9:00", "%H:%M"), 'end': datetime.strptime("10:30", "%H:%M")},
        {'start': datetime.strptime("11:00", "%H:%M"), 'end': datetime.strptime("11:30", "%H:%M")},
        {'start': datetime.strptime("12:00", "%H:%M"), 'end': datetime.strptime("14:00", "%H:%M")},
        {'start': datetime.strptime("15:00", "%H:%M"), 'end': datetime.strptime("16:00", "%H:%M")},
        {'start': datetime.strptime("16:30", "%H:%M"), 'end': datetime.strptime("17:00", "%H:%M")}
    ]
}

meeting_time, meeting_day = find_meeting_time(bobby_schedule, michael_schedule, 0.5, "9:00", "17:00", ["Monday", "Tuesday"])
print(f"{meeting_time}, {meeting_day}")