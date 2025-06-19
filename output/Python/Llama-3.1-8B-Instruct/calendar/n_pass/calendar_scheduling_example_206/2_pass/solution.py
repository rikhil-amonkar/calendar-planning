from datetime import datetime, timedelta

def find_available_time(start_time, end_time, schedules, meeting_duration):
    """
    Find a time that works for everyone's schedule and constraints.
    
    Args:
    start_time (datetime): Start time of the day.
    end_time (datetime): End time of the day.
    schedules (dict): Dictionary of participant schedules.
    meeting_duration (int): Duration of the meeting in minutes.
    
    Returns:
    tuple: Proposed start and end time of the meeting.
    """
    # Find all available time slots
    available_slots = []
    current_time = start_time
    while current_time < end_time:
        is_available = True
        for participant, schedule in schedules.items():
            for time_slot in schedule:
                if (current_time.time() >= time_slot[0] and current_time.time() < time_slot[1]) or \
                   (current_time + timedelta(minutes=meeting_duration).time() >= time_slot[0] and current_time + timedelta(minutes=meeting_duration).time() < time_slot[1]):
                    is_available = False
                    break
            if not is_available:
                break
        if is_available:
            available_slots.append((current_time, current_time + timedelta(minutes=meeting_duration)))
        current_time += timedelta(minutes=1)
    
    # Filter available slots based on Margaret's preference
    available_slots = [slot for slot in available_slots if slot[0].time() >= datetime.strptime('14:30', '%H:%M').time()]
    
    # Return the first available slot
    if available_slots:
        return available_slots[0]
    else:
        return None

def main():
    # Define participant schedules
    schedules = {
        'Shirley': [(datetime.strptime('10:30', '%H:%M').time(), datetime.strptime('11:00', '%H:%M').time()),
                    (datetime.strptime('12:00', '%H:%M').time(), datetime.strptime('12:30', '%H:%M').time())],
        'Jacob': [(datetime.strptime('9:00', '%H:%M').time(), datetime.strptime('9:30', '%H:%M').time()),
                  (datetime.strptime('10:00', '%H:%M').time(), datetime.strptime('10:30', '%H:%M').time()),
                  (datetime.strptime('11:00', '%H:%M').time(), datetime.strptime('11:30', '%H:%M').time()),
                  (datetime.strptime('12:30', '%H:%M').time(), datetime.strptime('13:30', '%H:%M').time()),
                  (datetime.strptime('14:30', '%H:%M').time(), datetime.strptime('15:00', '%H:%M').time())],
        'Stephen': [(datetime.strptime('11:30', '%H:%M').time(), datetime.strptime('12:00', '%H:%M').time()),
                    (datetime.strptime('12:30', '%H:%M').time(), datetime.strptime('13:00', '%H:%M').time())],
        'Margaret': [(datetime.strptime('9:00', '%H:%M').time(), datetime.strptime('9:30', '%H:%M').time()),
                     (datetime.strptime('10:30', '%H:%M').time(), datetime.strptime('12:30', '%H:%M').time()),
                     (datetime.strptime('13:00', '%H:%M').time(), datetime.strptime('13:30', '%H:%M').time()),
                     (datetime.strptime('15:00', '%H:%M').time(), datetime.strptime('15:30', '%H:%M').time()),
                     (datetime.strptime('16:30', '%H:%M').time(), datetime.strptime('17:00', '%H:%M').time())],
        'Mason': [(datetime.strptime('9:00', '%H:%M').time(), datetime.strptime('10:00', '%H:%M').time()),
                  (datetime.strptime('10:30', '%H:%M').time(), datetime.strptime('11:00', '%H:%M').time()),
                  (datetime.strptime('11:30', '%H:%M').time(), datetime.strptime('12:30', '%H:%M').time()),
                  (datetime.strptime('13:00', '%H:%M').time(), datetime.strptime('13:30', '%H:%M').time()),
                  (datetime.strptime('14:00', '%H:%M').time(), datetime.strptime('14:30', '%H:%M').time()),
                  (datetime.strptime('16:30', '%H:%M').time(), datetime.strptime('17:00', '%H:%M').time())]
    }
    
    # Define meeting duration
    meeting_duration = 30
    
    # Define start and end time of the day
    start_time = datetime.strptime('2024-07-29', '%Y-%m-%d').replace(hour=9, minute=0)
    end_time = datetime.strptime('2024-07-29', '%Y-%m-%d').replace(hour=17, minute=0)
    
    # Find available time
    available_time = find_available_time(start_time, end_time, schedules, meeting_duration)
    
    # Print result
    if available_time:
        print(f"{start_time.strftime('%A, %Y-%m-%d')} {available_time[0].strftime('%H:%M')} - {available_time[1].strftime('%H:%M')}")
    else:
        print("No available time found.")

if __name__ == "__main__":
    main()