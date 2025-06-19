from datetime import datetime, timedelta

def find_meeting_time(jesse_schedule, lawrence_schedule, meeting_duration):
    """
    Find a common available time slot for Jesse and Lawrence.

    Args:
        jesse_schedule (dict): Jesse's schedule, where each key is a day and each value is a list of time slots.
        lawrence_schedule (dict): Lawrence's schedule, where each key is a day and each value is a list of time slots.
        meeting_duration (int): The duration of the meeting in minutes.

    Returns:
        None
    """

    # Define the work hours
    start_time = datetime.strptime('09:00', '%H:%M')
    end_time = datetime.strptime('17:00')

    # Find available time slots for Jesse and Lawrence
    jesse_available_time = {}
    for day, schedule in jesse_schedule.items():
        jesse_available_time[day] = []
        for time in schedule:
            start_time_slot = datetime.strptime(time[0], '%H:%M')
            end_time_slot = datetime.strptime(time[1], '%H:%M')
            # Check if the time slot is within the work hours
            if start_time_slot >= start_time and end_time_slot <= end_time:
                jesse_available_time[day].append((start_time_slot, end_time_slot))
        
        jesse_available_time[day].sort()

    lawrence_available_time = {}
    for day, schedule in lawrence_schedule.items():
        lawrence_available_time[day] = []
        for time in schedule:
            start_time_slot = datetime.strptime(time[0], '%H:%M')
            end_time_slot = datetime.strptime(time[1], '%H:%M')
            # Check if the time slot is within the work hours
            if start_time_slot >= start_time and end_time_slot <= end_time:
                lawrence_available_time[day].append((start_time_slot, end_time_slot))
        
        lawrence_available_time[day].sort()

    # Find a time slot that is common to both Jesse and Lawrence
    for day in jesse_available_time:
        if day in lawrence_available_time:
            jesse_available_time_slots = jesse_available_time[day]
            lawrence_available_time_slots = lawrence_available_time[day]

            for i in range(len(jesse_available_time_slots)):
                for j in range(len(lawrence_available_time_slots)):
                    if jesse_available_time_slots[i][1] < lawrence_available_time_slots[j][0]:
                        continue
                    if lawrence_available_time_slots[j][1] < jesse_available_time_slots[i][0]:
                        continue
                    common_duration_minutes = (min(jesse_available_time_slots[i][1], lawrence_available_time_slots[j][1]) - max(jesse_available_time_slots[i][0], lawrence_available_time_slots[j][0])).total_seconds() / 60
                    if common_duration_minutes >= meeting_duration:
                        meeting_start_time = max(jesse_available_time_slots[i][0], lawrence_available_time_slots[j][0])
                        meeting_end_time = meeting_start_time + timedelta(minutes=meeting_duration)
                        print(f"Meeting time: {meeting_start_time.strftime('%H:%M')} - {meeting_end_time.strftime('%H:%M')}, Day: {day}")
                        return

    print("No common available time slot found.")

# Define the schedules for Jesse and Lawrence
jesse_schedule = {
    'Monday': [('09:00', '09:30'), ('10:00', '10:30'), ('11:00', '11:30'), ('12:00', '12:30'), ('13:30', '14:00'), ('14:30', '15:00')],
    'Tuesday': [('09:00', '09:30'), ('13:00', '13:30'), ('14:00', '15:00')]
}

lawrence_schedule = {
    'Monday': [('09:00', '17:00')],
    'Tuesday': [('09:30', '10:30'), ('11:30', '12:30'), ('13:00', '13:30'), ('14:30', '15:00'), ('15:30', '16:30')]
}

meeting_duration = 30  # in minutes

find_meeting_time(jesse_schedule, lawrence_schedule, meeting_duration)