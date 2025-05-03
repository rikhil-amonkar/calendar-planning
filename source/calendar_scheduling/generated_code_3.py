from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, meeting_duration, constraints):
    """
    Find a suitable time for a meeting based on the participants' schedules and constraints.
    
    Args:
    start_time (datetime): The start time of the workday.
    end_time (datetime): The end time of the workday.
    meeting_duration (timedelta): The duration of the meeting.
    constraints (list): A list of tuples representing the blocked time slots.
    
    Returns:
    tuple: A tuple containing the start and end times of the meeting.
    """
    
    # Iterate over all time slots in the workday
    for hour in range(int((end_time - start_time).total_seconds() / 3600)):
        time = start_time + timedelta(hours=hour)
        
        # Check if the current time slot is not blocked for both participants
        if not any(start <= time < end for start, end in constraints[0]) and not any(start <= time < end for start, end in constraints[1]):
            # Check if the current time slot can accommodate the meeting
            if time + meeting_duration <= end_time:
                return time, time + meeting_duration
    
    return None

def main():
    # Define the work hours
    start_time = datetime.strptime('09:00', '%H:%M')
    end_time = datetime.strptime('17:00', '%H:%M')
    
    # Define the meeting duration
    meeting_duration = timedelta(hours=1)
    
    # Define the constraints
    russell_constraints = [
        (datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
        (datetime.strptime('13:00', '%H:%M'), datetime.strptime('13:30', '%H:%M'))
    ]
    
    alexander_constraints = [
        (datetime.strptime('09:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
        (datetime.strptime('12:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
        (datetime.strptime('15:00', '%H:%M'), datetime.strptime('17:00', '%H:%M')),
        (datetime.strptime('09:00', '%H:%M'), datetime.strptime('10:00', '%H:%M')),
        (datetime.strptime('13:00', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
        (datetime.strptime('15:00', '%H:%M'), datetime.strptime('15:30', '%H:%M')),
        (datetime.strptime('16:00', '%H:%M'), datetime.strptime('16:30', '%H:%M'))
    ]
    
    # Find a suitable time for the meeting
    time = find_meeting_time(start_time, end_time, meeting_duration, [russell_constraints, alexander_constraints])
    
    if time:
        print(f"{time[0].strftime('%H:%M')}:{time[1].strftime('%H:%M')}")
    else:
        print("No suitable time found.")

if __name__ == "__main__":
    main()