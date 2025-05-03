from datetime import datetime, timedelta

def schedule_meeting(start_time, end_time, free_time, meeting_duration):
    # Find available time slots
    available_slots = []
    for time in free_time:
        start = datetime.strptime(time, '%H:%M')
        end = start + timedelta(minutes=meeting_duration)
        if start >= start_time and end <= end_time:
            available_slots.append((start.strftime('%H:%M'), end.strftime('%H:%M')))

    # Sort available slots by start time
    available_slots.sort(key=lambda x: x[0])

    # Find the first available slot
    proposed_time = available_slots[0]

    return proposed_time


# Input data
start_time = '09:00'
end_time = '17:00'
meeting_duration = 30  # minutes

# Daniel's schedule
daniel_blocked_time = ['10:00', '10:30', '11:00', '11:30']

# Donna's schedule
donna_blocked_time = ['10:30', '11:00', '11:30', '12:00', '12:30', '13:30', '14:00', '14:30', '15:00', '16:00', '16:30', '17:00']

# Find a proposed time that works for everyone's schedule and constraints
proposed_time = schedule_meeting(start_time, end_time, daniel_blocked_time, meeting_duration)
for time in donna_blocked_time:
    if time not in daniel_blocked_time:
        proposed_time = (time, str(int(time) + meeting_duration))
        break

print(f'Proposed meeting time: {proposed_time[0]}:{proposed_time[0]}:{proposed_time[1]}:{proposed_time[1]}')