import datetime

def find_meeting_time(participants, meeting_duration, preferred_day):
    # Convert schedules to time objects for easier manipulation
    free_times = []
    for person in participants:
        free = []
        for time in person:
            start = datetime.time(hour=time[0], minute=time[1])
            end = datetime.time(hour=time[2], minute=time[3])
            free.append((start, end))
        free_times.append(free)
    
    # Check each preferred day
    for day in preferred_day:
        day_free = True
        for i, person in enumerate(participants):
            for time in person:
                if time[0].date() == day.date():
                    start = time[0]
                    end = time[1]
                    if not (end < start + meeting_duration):
                        day_free = False
                        break
            if not day_free:
                break
        if day_free:
            for time in participants[0]:
                start = time[0]
                end = time[1]
                if start.date() == day.date() and end.date() == day.date():
                    return f"{start.strftime('%H:%M')}:{end.strftime('%H:%M')}: {day}"
    
    # If no time found (though problem states there is a solution)
    return "No time found"

# Example usage
participants = [
    [
        ("09:30", "10:30"),
        ("13:30", "14:30")
    ],
    [
        ("12:30", "13:00"),
        ("15:00", "15:30")
    ],
    [
        ("10:00", "10:30"),
        ("11:00", "11:30"),
        ("12:00", "12:30"),
        ("13:30", "14:00"),
        ("15:00", "16:00")
    ],
    [],
    [
        ("09:00", "09:30"),
        ("10:30", "12:00"),
        ("12:30", "13:00"),
        ("13:30", "15:00"),
        ("15:30", "16:00"),
        ("16:30", "17:00")
    ],
    [
        ("09:00", "11:00"),
        ("11:30", "13:00"),
        ("13:30", "14:00"),
        ("15:30", "16:00"),
        ("16:30", "17:00")
    ],
    [
        ("09:00", "09:30"),
        ("10:00", "11:30"),
        ("12:00", "13:30"),
        ("14:00", "16:00"),
        ("16:30", "17:00")
    ]
]

meeting_duration = datetime.timedelta(minutes=30)
preferred_day = ["Monday"]

print(find_meeting_time(participants, meeting_duration, preferred_day))