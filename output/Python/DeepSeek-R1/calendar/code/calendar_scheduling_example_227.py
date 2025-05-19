def main():
    work_hours = ('09:00', '17:00')
    participants = {
        'Natalie': [],
        'David': [('11:30', '12:00'), ('14:30', '15:00')],
        'Douglas': [('09:30', '10:00'), ('11:30', '12:00'), ('13:00', '13:30'), ('14:30', '15:00')],
        'Ralph': [('09:00', '09:30'), ('10:00', '11:00'), ('11:30', '12:30'), ('13:30', '15:00'), ('15:30', '16:00'), ('16:30', '17:00')],
        'Jordan': [('09:00', '10:00'), ('12:00', '12:30'), ('13:00', '13:30'), ('14:30', '15:00'), ('15:30', '17:00')]
    }
    preferences = {'David': [('00:00', '14:00')]}
    duration = 30

    def time_to_minutes(t):
        h, m = map(int, t.split(':'))
        return h * 60 + m

    work_start = time_to_minutes(work_hours[0])
    work_end = time_to_minutes(work_hours[1])

    busy_slots = []
    for person, slots in participants.items():
        for start, end in slots:
            busy_slots.append((time_to_minutes(start), time_to_minutes(end)))

    for person, pref in preferences.items():
        for start, end in pref:
            busy_slots.append((time_to_minutes(start), time_to_minutes(end)))

    free_slots = []
    current = work_start
    for start, end in sorted(busy_slots, key=lambda x: x[0]):
        if start > current:
            free_slots.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_slots.append((current, work_end))

    valid_slots = []
    for start, end in free_slots:
        if end - start >= duration:
            valid_slots.append((start, end))

    def minutes_to_time(m):
        return f"{m // 60:02d}:{m % 60:02d}"

    meeting_slot = None
    for slot in valid_slots:
        slot_start, slot_end = slot
        if slot_end - slot_start >= duration:
            meeting_start = slot_start
            meeting_end = meeting_start + duration
            conflict = False
            for person, slots in participants.items():
                for s, e in slots:
                    s_m = time_to_minutes(s)
                    e_m = time_to_minutes(e)
                    if not (meeting_end <= s_m or meeting_start >= e_m):
                        conflict = True
                        break
                if person in preferences:
                    for s, e in preferences[person]:
                        s_m = time_to_minutes(s)
                        e_m = time_to_minutes(e)
                        if not (meeting_end <= s_m or meeting_start >= e_m):
                            conflict = True
                            break
                if conflict:
                    break
            if not conflict:
                meeting_slot = (meeting_start, meeting_end)
                break

    if meeting_slot:
        start = minutes_to_time(meeting_slot[0])
        end = minutes_to_time(meeting_slot[1])
        print(f"Monday {start}:{end}")

if __name__ == "__main__":
    main()