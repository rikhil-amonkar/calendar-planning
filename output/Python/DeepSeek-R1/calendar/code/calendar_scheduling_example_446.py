def find_meeting_time():
    work_hours = (9, 17)
    participants = {
        'Megan': [(9, 9.5), (10, 11), (12, 12.5)],
        'Christine': [(9, 9.5), (11.5, 12), (13, 14), (15.5, 16.5)],
        'Gabriel': [],
        'Sara': [(11.5, 12), (14.5, 15)],
        'Bruce': [(9.5, 10), (10.5, 12), (12.5, 14), (14.5, 15), (15.5, 16.5)],
        'Kathryn': [(10, 15.5), (16, 16.5)],
        'Billy': [(9, 9.5), (11, 11.5), (12, 14), (14.5, 15.5)]
    }

    for hour in range(work_hours[0], work_hours[1]):
        for minute in [0, 0.5]:
            start = hour + minute
            end = start + 0.5
            if end > work_hours[1]:
                continue
            all_free = True
            for busy in participants.values():
                for slot in busy:
                    if start < slot[1] and end > slot[0]:
                        all_free = False
                        break
                if not all_free:
                    break
            if all_free:
                def format_time(t):
                    hours = int(t)
                    minutes = int((t - hours) * 60)
                    return f"{hours:02d}:{minutes:02d}"
                return f"Monday {format_time(start)}-{format_time(end)}"
    return "No time found"

print(find_meeting_time())