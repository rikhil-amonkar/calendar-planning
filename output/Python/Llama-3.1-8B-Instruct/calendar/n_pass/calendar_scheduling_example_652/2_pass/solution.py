from datetime import datetime, timedelta

def find_meeting_time(jesse_schedule, lawrence_schedule, meeting_duration):
    # Define the work hours
    start_time = datetime.strptime('09:00', '%H:%M')
    end_time = datetime.strptime('17:00', '%H:%M')

    # Find available time slots for Jesse and Lawrence
    jesse_available_time = []
    for day, schedule in jesse_schedule.items():
        for time in schedule:
            start_time_slot = datetime.strptime(time[0], '%H:%M')
            end_time_slot = datetime.strptime(time[1], '%H:%M')
            jesse_available_time.append((start_time + timedelta(hours=start_time_slot.hour, minutes=start_time_slot.minute),
                                         end_time + timedelta(hours=end_time_slot.hour, minutes=end_time_slot.minute)))
        
        jesse_available_time.sort()

    lawrence_available_time = []
    for day, schedule in lawrence_schedule.items():
        for time in schedule:
            start_time_slot = datetime.strptime(time[0], '%H:%M')
            end_time_slot = datetime.strptime(time[1], '%H:%M')
            lawrence_available_time.append((start_time + timedelta(hours=start_time_slot.hour, minutes=start_time_slot.minute),
                                            end_time + timedelta(hours=end_time_slot.hour, minutes=end_time_slot.minute)))
        
        lawrence_available_time.sort()

    # Find a time slot that is common to both Jesse and Lawrence
    for i in range(len(jesse_available_time)):
        for j in range(len(lawrence_available_time)):
            if jesse_available_time[i][1] < lawrence_available_time[j][0]:
                continue
            if lawrence_available_time[j][1] < jesse_available_time[i][0]:
                continue
            if jesse_available_time[i][0] >= start_time and jesse_available_time[i][1] <= end_time:
                if lawrence_available_time[j][0] >= start_time and lawrence_available_time[j][1] <= end_time:
                    if lawrence_available_time[j][0] + timedelta(minutes=meeting_duration) <= jesse_available_time[i][1]:
                        meeting_start_time = jesse_available_time[i][0]
                        meeting_end_time = meeting_start_time + timedelta(minutes=meeting_duration)
                        print(f"Meeting time: {meeting_start_time.strftime('%H:%M')} - {meeting_end_time.strftime('%H:%M')}, Day: {day}")
                        return
            else:
                continue
            if lawrence_available_time[j][0] >= start_time and lawrence_available_time[j][1] <= end_time:
                meeting_start_time = lawrence_available_time[j][0]
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