from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, duration, schedules):
    """
    Find a time that works for everyone's schedule and constraints.
    
    Args:
        start_time (datetime): The start time of the day.
        end_time (datetime): The end time of the day.
        duration (int): The duration of the meeting in minutes.
        schedules (dict): A dictionary of participants and their schedules.
        
    Returns:
        tuple: A tuple containing the start and end time of the meeting, and the day of the week.
    """
    # Generate a list of time slots
    time_slots = [(start_time + timedelta(minutes=i)).time() for i in range(0, (end_time - start_time).seconds // 60 + 1)]
    
    # Filter out time slots that don't work for each participant
    for participant, schedule in schedules.items():
        time_slots = [slot for slot in time_slots if not any(start <= slot <= end for start, end in schedule)]
    
    # Find the first available time slot that is long enough for the meeting
    for i in range(len(time_slots) - duration // 60):
        if time_slots[i] == time_slots[i + duration // 60]:
            return (start_time + timedelta(minutes=i), start_time + timedelta(minutes=i + duration)), start_time.strftime("%A")

def main():
    # Define the schedules for each participant
    andrew_schedule = []
    grace_schedule = []
    samuel_schedule = [(datetime(2024, 7, 22, 9), datetime(2024, 7, 22, 10, 30)),
                       (datetime(2024, 7, 22, 11, 30), datetime(2024, 7, 22, 12)),
                       (datetime(2024, 7, 22, 13), datetime(2024, 7, 22, 13, 30)),
                       (datetime(2024, 7, 22, 14), datetime(2024, 7, 22, 16)),
                       (datetime(2024, 7, 22, 16, 30), datetime(2024, 7, 22, 17))]
    
    # Define the start and end time of the day
    start_time = datetime(2024, 7, 22, 9)
    end_time = datetime(2024, 7, 22, 17)
    
    # Define the duration of the meeting
    duration = 30
    
    # Find the meeting time
    meeting_time, day_of_week = find_meeting_time(start_time, end_time, duration, {'Andrew': andrew_schedule, 'Grace': grace_schedule, 'Samuel': samuel_schedule})
    
    # Print the meeting time and day of the week
    print(f"{meeting_time[0].strftime('%H:%M')} - {meeting_time[1].strftime('%H:%M')}, {day_of_week}")

if __name__ == "__main__":
    main()