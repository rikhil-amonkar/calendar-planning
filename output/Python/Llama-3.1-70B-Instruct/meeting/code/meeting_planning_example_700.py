import json
from datetime import datetime, timedelta

# Define travel times between locations
travel_times = {
    'Presidio': {'Pacific Heights': 11, 'Golden Gate Park': 12, 'Fisherman\'s Wharf': 19, 'Marina District': 11, 'Alamo Square': 19, 'Sunset District': 15, 'Nob Hill': 18, 'North Beach': 18},
    'Pacific Heights': {'Presidio': 11, 'Golden Gate Park': 15, 'Fisherman\'s Wharf': 13, 'Marina District': 6, 'Alamo Square': 10, 'Sunset District': 21, 'Nob Hill': 8, 'North Beach': 9},
    'Golden Gate Park': {'Presidio': 11, 'Pacific Heights': 16, 'Fisherman\'s Wharf': 24, 'Marina District': 16, 'Alamo Square': 9, 'Sunset District': 10, 'Nob Hill': 20, 'North Beach': 23},
    'Fisherman\'s Wharf': {'Presidio': 17, 'Pacific Heights': 12, 'Golden Gate Park': 25, 'Marina District': 9, 'Alamo Square': 21, 'Sunset District': 27, 'Nob Hill': 11, 'North Beach': 6},
    'Marina District': {'Presidio': 10, 'Pacific Heights': 7, 'Golden Gate Park': 18, 'Fisherman\'s Wharf': 10, 'Alamo Square': 15, 'Sunset District': 19, 'Nob Hill': 12, 'North Beach': 11},
    'Alamo Square': {'Presidio': 17, 'Pacific Heights': 10, 'Golden Gate Park': 9, 'Fisherman\'s Wharf': 19, 'Marina District': 15, 'Sunset District': 16, 'Nob Hill': 11, 'North Beach': 15},
    'Sunset District': {'Presidio': 16, 'Pacific Heights': 21, 'Golden Gate Park': 11, 'Fisherman\'s Wharf': 29, 'Marina District': 21, 'Alamo Square': 17, 'Nob Hill': 27, 'North Beach': 28},
    'Nob Hill': {'Presidio': 17, 'Pacific Heights': 8, 'Golden Gate Park': 17, 'Fisherman\'s Wharf': 10, 'Marina District': 11, 'Alamo Square': 11, 'Sunset District': 24, 'North Beach': 8},
    'North Beach': {'Presidio': 17, 'Pacific Heights': 8, 'Golden Gate Park': 22, 'Fisherman\'s Wharf': 5, 'Marina District': 9, 'Alamo Square': 16, 'Sunset District': 27, 'Nob Hill': 7}
}

# Define meeting constraints
meetings = [
    {'person': 'Kevin', 'location': 'Pacific Heights','start_time': '07:15', 'end_time': '08:45','min_time': 90},
    {'person': 'Michelle', 'location': 'Golden Gate Park','start_time': '20:00', 'end_time': '21:00','min_time': 15},
    {'person': 'Emily', 'location': 'Fisherman\'s Wharf','start_time': '16:15', 'end_time': '19:00','min_time': 30},
    {'person': 'Mark', 'location': 'Marina District','start_time': '18:15', 'end_time': '19:45','min_time': 75},
    {'person': 'Barbara', 'location': 'Alamo Square','start_time': '17:00', 'end_time': '19:00','min_time': 120},
    {'person': 'Laura', 'location': 'Sunset District','start_time': '19:00', 'end_time': '21:15','min_time': 75},
    {'person': 'Mary', 'location': 'Nob Hill','start_time': '17:30', 'end_time': '19:00','min_time': 45},
    {'person': 'Helen', 'location': 'North Beach','start_time': '11:00', 'end_time': '12:15','min_time': 45}
]

def calculate_meeting_schedule(meetings, travel_times):
    schedule = []
    current_time = datetime.strptime('09:00', '%H:%M')
    current_location = 'Presidio'

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