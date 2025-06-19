from datetime import datetime, timedelta

def find_meeting_time(larry_availability, samuel_availability, larry_preferences, samuel_preferences):
    """
    Find a suitable time for a meeting based on the participants' schedules and constraints.
    
    Parameters:
    larry_availability (list): Larry's availability in the format [(day, start, end),...]
    samuel_availability (list): Samuel's availability in the format [(day, start, end),...]
    larry_preferences (list): Larry's preferences in the format [(day, time),...]
    samuel_preferences (list): Samuel's preferences in the format [(day, time),...]
    
    Returns:
    tuple: A proposed meeting time in the format (day, start, end) and the day of the week
    """
    
    # Filter out unavailable days for Larry and Samuel
    larry_availability = [(day, start, end) for day, start, end in larry_availability 
                          if start < end and (day == 'Monday' or day == 'Tuesday' or day == 'Wednesday')]
    samuel_availability = [(day, start, end) for day, start, end in samuel_availability 
                           if start < end and (day == 'Monday' or day == 'Tuesday' or day == 'Wednesday')]
    
    # Sort the availability by day and start time
    larry_availability.sort(key=lambda x: (x[0], x[1]))
    samuel_availability.sort(key=lambda x: (x[0], x[1]))
    
    # Find the earliest available time for both Larry and Samuel
    larry_start = larry_availability[0][1]
    samuel_start = samuel_availability[0][1]
    
    # Find the latest available time for both Larry and Samuel
    larry_end = larry_availability[-1][2]
    samuel_end = samuel_availability[-1][2]
    
    # Check Larry's preferences
    larry_preferred_days = [day for day, time in larry_preferences]
    if 'Monday' in larry_preferred_days:
        larry_start = max(larry_start, 9 * 60)
        larry_end = min(larry_end, 17 * 60 - 30)
    if 'Tuesday' in larry_preferred_days:
        larry_start = max(larry_start, 9 * 60)
        larry_end = min(larry_end, 17 * 60 - 30)
    if 'Wednesday' in larry_preferred_days:
        larry_start = max(larry_start, 9 * 60)
        larry_end = min(larry_end, 17 * 60 - 30)
    
    # Check Samuel's preferences
    samuel_preferred_days = [day for day, time in samuel_preferences]
    if 'Monday' in samuel_preferred_days:
        samuel_start = max(samuel_start, 9 * 60)
        samuel_end = min(samuel_end, 17 * 60 - 30)
    if 'Tuesday' in samuel_preferred_days:
        samuel_start = max(samuel_start, 9 * 60)
        samuel_end = min(samuel_end, 17 * 60 - 30)
    if 'Wednesday' in samuel_preferred_days:
        samuel_start = max(samuel_start, 9 * 60)
        samuel_end = min(samuel_end, 17 * 60 - 30)
    
    # Find the earliest available time that works for both Larry and Samuel
    for day in ['Monday', 'Tuesday', 'Wednesday']:
        if day in larry_preferred_days and day in samuel_preferred_days:
            if day == 'Monday':
                start = max(larry_start, samuel_start)
                end = min(larry_end, samuel_end)
                if start < end:
                    return day, start, end, day
            elif day == 'Tuesday':
                start = max(larry_start, samuel_start)
                end = min(larry_end, samuel_end)
                if start < end and samuel_end - samuel_start > 30:
                    return day, start, end, day
            elif day == 'Wednesday':
                start = max(larry_start, samuel_start)
                end = min(larry_end, samuel_end)
                if start < end:
                    return day, start, end, day
    
    # If no available time is found, return None
    return None

def main():
    # Define the availability and preferences for Larry and Samuel
    larry_availability = [('Monday', 0 * 60, 24 * 60), ('Tuesday', 0 * 60, 24 * 60), ('Wednesday', 0 * 60, 24 * 60)]
    samuel_availability = [('Monday', 10 * 60, 15 * 60), ('Monday', 12 * 60, 12 * 30 + 12 * 60), 
                           ('Monday', 13 * 60, 15 * 60), ('Monday', 15 * 30 + 12 * 60, 16 * 30 + 12 * 60), 
                           ('Tuesday', 9 * 60, 12 * 60), ('Tuesday', 14 * 60, 15 * 30 + 12 * 60), 
                           ('Tuesday', 16 * 30 + 12 * 60, 17 * 60), 
                           ('Wednesday', 10 * 60, 11 * 60), ('Wednesday', 11 * 30 + 12 * 60, 12 * 60), 
                           ('Wednesday', 12 * 30 + 12 * 60, 13 * 60), 
                           ('Wednesday', 14 * 60, 14 * 30 + 12 * 60), ('Wednesday', 15 * 60, 16 * 60)]
    larry_preferences = [('Monday', 9 * 60), ('Tuesday', 9 * 60), ('Wednesday', 9 * 60)]
    samuel_preferences = [('Monday', 9 * 60), ('Tuesday', 9 * 60), ('Wednesday', 9 * 60)]
    
    # Find a proposed meeting time
    proposed_time = find_meeting_time(larry_availability, samuel_availability, larry_preferences, samuel_preferences)
    
    # Print the proposed meeting time
    if proposed_time:
        day, start, end, day_of_week = proposed_time
        print(f"Proposed meeting time: {day_of_week}, {datetime.fromtimestamp(start / 60).strftime('%H:%M')} - {datetime.fromtimestamp(end / 60).strftime('%H:%M')}")
    else:
        print("No available time found.")

if __name__ == "__main__":
    main()