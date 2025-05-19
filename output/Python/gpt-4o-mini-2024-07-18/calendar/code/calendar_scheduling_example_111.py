from datetime import datetime, timedelta

# Participants' schedules
gregory_schedule = [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('10:00', '%H:%M')),
                    (datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
                    (datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
                    (datetime.strptime('13:30', '%H:%M'), datetime.strptime('14:00', '%H:%M'))]

natalie_schedule = []  # Natalie is available all day

christine_schedule = [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
                      (datetime.strptime('13:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))]

vincent_schedule = [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
                    (datetime.strptime('10:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
                    (datetime.strptime('12:30', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
                    (datetime.strptime('14:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))]

# Work hours
work_start = datetime.strptime('09:00', '%H:%M')
work_end = datetime.strptime('17:00', '%H:%M')
meeting_duration = timedelta(minutes=30)

# Find available slots
def find_available_slots(schedule):
    available_slots = []
    current_time = work_start

    for start, end in sorted(schedule):
        # Check for time slot before this blocked time
        if current_time < start:
            available_slots.append((current_time, start))
        current_time = max(current_time, end)

    # Check for any available time after the last meeting until end of work hours
    if current_time < work_end:
        available_slots.append((current_time, work_end))
    
    return available_slots

# Get available slots for each participant
gregory_slots = find_available_slots(gregory_schedule)
natalie_slots = [(work_start, work_end)]  # Natalie is available all day
christine_slots = find_available_slots(christine_schedule)
vincent_slots = find_available_slots(vincent_schedule)

# Function to find a common available meeting time
def find_meeting_time(slots_list):
    for start, end in slots_list[0]:
        # Check if this slot can fit all other schedules
        meeting_time = start
        if meeting_time + meeting_duration <= end:  # First person time slot
            can_schedule = True
            for slots in slots_list[1:]:
                # Check for availability in other participants' slots
                if not any(s_start <= meeting_time < s_end for s_start, s_end in slots):
                    can_schedule = False
                    break
            if can_schedule:
                return meeting_time
    return None

# Collecting all available slots
all_slots = [gregory_slots, natalie_slots, christine_slots, vincent_slots]

# Finding meeting time
meeting_start = find_meeting_time(all_slots)
meeting_end = meeting_start + meeting_duration

# Output result
if meeting_start:
    day_of_week = "Monday"
    print(f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')} - {day_of_week}")