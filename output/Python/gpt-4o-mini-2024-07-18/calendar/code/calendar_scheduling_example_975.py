from datetime import datetime, timedelta

# Participants' schedules
schedule_nicole = {
    'Tuesday': [(16, 0, 16, 30)],
    'Wednesday': [(15, 0, 15, 30)],
    'Friday': [(12, 0, 12, 30), (15, 30, 16, 0)]
}

schedule_daniel = {
    'Monday': [(9, 0, 12, 30), (13, 0, 13, 30), (14, 0, 16, 30)],
    'Tuesday': [(9, 0, 10, 30), (11, 30, 12, 30), (13, 0, 13, 30), (15, 0, 16, 0), (16, 30, 17, 0)],
    'Wednesday': [(9, 0, 10, 0), (11, 0, 12, 30), (13, 0, 13, 30), (14, 0, 14, 30), (16, 30, 17, 0)],
    'Thursday': [(11, 0, 12, 0), (13, 0, 14, 0), (15, 0, 15, 30)],
    'Friday': [(10, 0, 11, 0), (11, 30, 12, 0), (12, 30, 14, 30), (15, 0, 15, 30), (16, 0, 16, 30)]
}

# Calculate available slots
def get_available_slots(schedule, work_start, work_end):
    available_slots = {}
    for day in ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']:
        busy_times = schedule.get(day, [])
        busy_times.sort()  # Sort by start time
        available_slots[day] = []
        
        # Assuming work hours
        start_of_day = (work_start.hour, work_start.minute)
        end_of_day = (work_end.hour, work_end.minute)

        # Start looking for availability
        last_end_time = start_of_day

        for busy in busy_times:
            busy_start = (busy[0], busy[1])
            busy_end = (busy[2], busy[3])

            # Check for free slot before the busy time
            if last_end_time < busy_start:
                available_slots[day].append((last_end_time[0], last_end_time[1], busy_start[0], busy_start[1]))
            
            last_end_time = busy_end
        
        # Check for free slot after all busy times until end of the day
        if last_end_time < end_of_day:
            available_slots[day].append((last_end_time[0], last_end_time[1], end_of_day[0], end_of_day[1]))

    return available_slots

def find_meeting_time():
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    available_nicole = get_available_slots(schedule_nicole, work_start, work_end)
    available_daniel = get_available_slots(schedule_daniel, work_start, work_end)

    # Find overlapping slots of at least 1 hour
    for day in available_nicole:
        nicole_slots = available_nicole[day]
        daniel_slots = available_daniel[day]

        for n_slot in nicole_slots:
            n_start = timedelta(hours=n_slot[0], minutes=n_slot[1])
            n_end = timedelta(hours=n_slot[2], minutes=n_slot[3])
            duration = n_end - n_start
            
            if duration >= timedelta(hours=1):  # Need at least 1 hour
                for d_slot in daniel_slots:
                    d_start = timedelta(hours=d_slot[0], minutes=d_slot[1])
                    d_end = timedelta(hours=d_slot[2], minutes=d_slot[3])
                    
                    # Check if the slots overlap
                    if d_start < n_end and n_start < d_end:
                        # Determine the meeting time
                        meeting_start_hours = max(n_slot[0], d_slot[0])
                        meeting_start_minutes = max(n_slot[1], d_slot[1])
                        
                        meeting_end_hours = meeting_start_hours + 1
                        meeting_end_minutes = meeting_start_minutes

                        if meeting_end_minutes >= 60:
                            meeting_end_minutes -= 60
                            meeting_end_hours += 1

                        if meeting_end_hours > 17:  # Ensure meeting does not exceed work time
                            continue

                        return f"{day} {meeting_start_hours:02}:{meeting_start_minutes:02}:{meeting_end_hours:02}:{meeting_end_minutes:02}"

# Generate proposed meeting time
proposed_time = find_meeting_time()
print(proposed_time)