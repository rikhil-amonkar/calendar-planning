from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration):
    # Sort participants by their earliest available time
    participants.sort(key=lambda x: min([start for start, end in x['schedules']]))
    
    # Initialize the earliest available time
    earliest_time = min([start for start, end in participants[0]['schedules']])
    
    # Iterate over the participants to find a common available time
    for participant in participants[1:]:
        for start, end in participant['schedules']:
            if start >= earliest_time:
                earliest_time = start
                break
        else:
            # If no available time is found, try the next day
            earliest_time += timedelta(days=1)
            for participant in participants:
                for start, end in participant['schedules']:
                    if start >= earliest_time:
                        earliest_time = start
                        break
                else:
                    # If no available time is found, try the next day
                    earliest_time += timedelta(days=1)
                    
    # Check if the earliest available time is within the work hours
    if earliest_time < datetime(1900, 1, 1, 9, 0) or earliest_time > datetime(1900, 1, 1, 17, 0):
        earliest_time = datetime(1900, 1, 1, 9, 0)
    
    # Calculate the meeting time
    meeting_time = (earliest_time + timedelta(minutes=meeting_duration)).strftime('%H:%M')
    end_time = (earliest_time + timedelta(minutes=meeting_duration)).strftime('%H:%M')
    
    # Format the output
    output = f"{participants[0]['name']} found a meeting time: {datetime(1900, 1, 1, 9, 0).strftime('%A')} {meeting_time}:{end_time}"
    
    return output

# Define the participants and their schedules
participants = [
    {'name': 'Emily','schedules': [(datetime(1900, 1, 1, 10, 0), datetime(1900, 1, 1, 10, 30)), (datetime(1900, 1, 1, 16, 0), datetime(1900, 1, 1, 16, 30))]},
    {'name': 'Mason','schedules': []},
    {'name': 'Maria','schedules': [(datetime(1900, 1, 1, 10, 30), datetime(1900, 1, 1, 11, 0)), (datetime(1900, 1, 1, 14, 0), datetime(1900, 1, 1, 14, 30))]},
    {'name': 'Carl','schedules': [(datetime(1900, 1, 1, 9, 30), datetime(1900, 1, 1, 10, 0)), (datetime(1900, 1, 1, 10, 30), datetime(1900, 1, 1, 12, 30)), (datetime(1900, 1, 1, 13, 30), datetime(1900, 1, 1, 14, 0)), (datetime(1900, 1, 1, 14, 30), datetime(1900, 1, 1, 15, 30)), (datetime(1900, 1, 1, 16, 0), datetime(1900, 1, 1, 17, 0))]},
    {'name': 'David','schedules': [(datetime(1900, 1, 1, 9, 30), datetime(1900, 1, 1, 11, 0)), (datetime(1900, 1, 1, 11, 30), datetime(1900, 1, 1, 12, 0)), (datetime(1900, 1, 1, 12, 30), datetime(1900, 1, 1, 13, 30)), (datetime(1900, 1, 1, 14, 0), datetime(1900, 1, 1, 15, 0)), (datetime(1900, 1, 1, 16, 0), datetime(1900, 1, 1, 17, 0))]},
    {'name': 'Frank','schedules': [(datetime(1900, 1, 1, 9, 30), datetime(1900, 1, 1, 10, 30)), (datetime(1900, 1, 1, 11, 0), datetime(1900, 1, 1, 11, 30)), (datetime(1900, 1, 1, 12, 30), datetime(1900, 1, 1, 13, 30)), (datetime(1900, 1, 1, 14, 30), datetime(1900, 1, 1, 17, 0))]}
]

# Find a meeting time
meeting_duration = 30  # in minutes
print(find_meeting_time(participants, meeting_duration))