import json
from datetime import datetime, timedelta

# Define travel times between locations
travel_times = {
    'Financial District': {'Fisherman\'s Wharf': 10, 'Pacific Heights': 13, 'Mission District': 17},
    'Fisherman\'s Wharf': {'Financial District': 11, 'Pacific Heights': 12, 'Mission District': 22},
    'Pacific Heights': {'Financial District': 13, 'Fisherman\'s Wharf': 13, 'Mission District': 15},
    'Mission District': {'Financial District': 17, 'Fisherman\'s Wharf': 22, 'Pacific Heights': 16}
}

# Define meeting constraints
meetings = [
    {'person': 'David', 'location': 'Fisherman\'s Wharf','start_time': '10:45', 'end_time': '15:30','min_time': 15},
    {'person': 'Timothy', 'location': 'Pacific Heights','start_time': '09:00', 'end_time': '15:30','min_time': 75},
    {'person': 'Robert', 'location': 'Mission District','start_time': '12:15', 'end_time': '19:45','min_time': 90}
]

def calculate_meeting_schedule(meetings, travel_times):
    schedule = []
    current_time = datetime.strptime('09:00', '%H:%M')
    current_location = 'Financial District'

    for meeting in meetings:
        # Calculate travel time to meeting location
        travel_time = travel_times[current_location][meeting['location']]
        arrival_time = current_time + timedelta(minutes=travel_time)

        # Check if meeting can be attended
        meeting_start_time = datetime.strptime(meeting['start_time'], '%H:%M')
        meeting_end_time = datetime.strptime(meeting['end_time'], '%H:%M')
        if arrival_time < meeting_end_time and arrival_time + timedelta(minutes=meeting['min_time']) <= meeting_end_time:
            # Attend meeting
            meeting_end = min(arrival_time + timedelta(minutes=meeting['min_time']), meeting_end_time)
            schedule.append({
                'action':'meet',
                'location': meeting['location'],
                'person': meeting['person'],
             'start_time': arrival_time.strftime('%H:%M'),
                'end_time': meeting_end.strftime('%H:%M')
            })
            current_time = meeting_end
            current_location = meeting['location']
        else:
            # Skip meeting
            continue

    return schedule

# Calculate and print meeting schedule
schedule = calculate_meeting_schedule(meetings, travel_times)
print(json.dumps({'itinerary': schedule}, indent=4))