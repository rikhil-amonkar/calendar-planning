import datetime

# Define participants' schedules
nancy_schedule = {
    "Monday": ["10:00-10:30", "11:30-12:30", "13:30-14:00", "14:30-15:30", "16:00-17:00"],
    "Tuesday": ["09:30-10:30", "11:00-11:30", "12:00-12:30", "13:00-13:30", "15:30-16:00"],
    "Wednesday": ["10:00-11:30", "13:30-16:00"]
}

jose_schedule = {
    "Monday": ["09:00-17:00"],
    "Tuesday": ["09:00-17:00"],
    "Wednesday": ["09:00-09:30", "10:00-12:30", "13:30-14:30", "15:00-17:00"]
}

# Define working hours and meeting duration
working_hours = {
    "Monday": ["09:00", "17:00"],
    "Tuesday": ["09:00", "17:00"],
    "Wednesday": ["09:00", "17:00"]
}
meeting_duration = datetime.timedelta(minutes=30)

def parse_schedule(schedule):
    busy_times = []
    for times in schedule.values():
        for time in times:
            start, end = time.split('-')
            busy_times.append((datetime.datetime.strptime(start, "%H:%M"), datetime.datetime.strptime(end, "%H:%M")))
    return busy_times

def find_time(participant1_schedule, participant2_schedule, working_hours):
    participant1_busy = parse_schedule(participant1_schedule)
    participant2_busy = parse_schedule(participant2_schedule)
    
    for day in working_hours:
        start_work, end_work = [datetime.datetime.strptime(t, "%H:%M") for t in working_hours[day]]
        available_slots = [(start_work, end_work)]
        
        # Mark busy slots
        for busy in participant1_busy + participant2_busy:
            new_available_slots = []
            for available in available_slots:
                if busy[0] > available[0]:
                    new_available_slots.append((available[0], min(busy[0], available[1])))
                if busy[1] < available[1]:
                    new_available_slots.append((max(busy[1], available[0]), available[1]))
            available_slots = new_available_slots
        
        # Find suitable meeting time
        for start, end in available_slots:
            if end - start >= meeting_duration:
                proposed_start = start
                proposed_end = start + meeting_duration
                return f"{proposed_start.strftime('%H:%M')}:{proposed_end.strftime('%H:%M')} {day}"
    
    return None

# Find the meeting time
meeting_time = find_time(nancy_schedule, jose_schedule, working_hours)

print(meeting_time)