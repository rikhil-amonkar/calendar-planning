import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(dt):
    return dt.strftime('%-H:%M')

def calculate_schedule():
    # Travel times dictionary: {from: {to: minutes}}
    travel_times = {
        'Mission District': {
            'Alamo Square': 11, 'Presidio': 25, 'Russian Hill': 15, 'North Beach': 17,
            'Golden Gate Park': 17, 'Richmond District': 20, 'Embarcadero': 19,
            'Financial District': 15, 'Marina District': 19
        },
        'Alamo Square': {
            'Mission District': 10, 'Presidio': 17, 'Russian Hill': 13, 'North Beach': 15,
            'Golden Gate Park': 9, 'Richmond District': 11, 'Embarcadero': 16,
            'Financial District': 17, 'Marina District': 15
        },
        'Presidio': {
            'Mission District': 26, 'Alamo Square': 19, 'Russian Hill': 14, 'North Beach': 18,
            'Golden Gate Park': 12, 'Richmond District': 7, 'Embarcadero': 20,
            'Financial District': 23, 'Marina District': 11
        },
        'Russian Hill': {
            'Mission District': 16, 'Alamo Square': 15, 'Presidio': 14, 'North Beach': 5,
            'Golden Gate Park': 21, 'Richmond District': 14, 'Embarcadero': 8,
            'Financial District': 11, 'Marina District': 7
        },
        'North Beach': {
            'Mission District': 18, 'Alamo Square': 16, 'Presidio': 17, 'Russian Hill': 4,
            'Golden Gate Park': 22, 'Richmond District': 18, 'Embarcadero': 6,
            'Financial District': 8, 'Marina District': 9
        },
        'Golden Gate Park': {
            'Mission District': 17, 'Alamo Square': 9, 'Presidio': 11, 'Russian Hill': 19,
            'North Beach': 23, 'Richmond District': 7, 'Embarcadero': 25,
            'Financial District': 26, 'Marina District': 16
        },
        'Richmond District': {
            'Mission District': 20, 'Alamo Square': 13, 'Presidio': 7, 'Russian Hill': 13,
            'North Beach': 17, 'Golden Gate Park': 9, 'Embarcadero': 19,
            'Financial District': 22, 'Marina District': 9
        },
        'Embarcadero': {
            'Mission District': 20, 'Alamo Square': 19, 'Presidio': 20, 'Russian Hill': 8,
            'North Beach': 5, 'Golden Gate Park': 25, 'Richmond District': 21,
            'Financial District': 5, 'Marina District': 12
        },
        'Financial District': {
            'Mission District': 17, 'Alamo Square': 17, 'Presidio': 22, 'Russian Hill': 11,
            'North Beach': 7, 'Golden Gate Park': 23, 'Richmond District': 21,
            'Embarcadero': 4, 'Marina District': 17
        },
        'Marina District': {
            'Mission District': 20, 'Alamo Square': 15, 'Presidio': 10, 'Russian Hill': 8,
            'North Beach': 11, 'Golden Gate Park': 18, 'Richmond District': 11,
            'Embarcadero': 14, 'Financial District': 17
        }
    }

    # Friend constraints
    friends = [
        {'name': 'Laura', 'location': 'Alamo Square', 'start': '14:30', 'end': '16:15', 'duration': 75},
        {'name': 'Brian', 'location': 'Presidio', 'start': '10:15', 'end': '17:00', 'duration': 30},
        {'name': 'Karen', 'location': 'Russian Hill', 'start': '18:00', 'end': '20:15', 'duration': 90},
        {'name': 'Stephanie', 'location': 'North Beach', 'start': '10:15', 'end': '16:00', 'duration': 75},
        {'name': 'Helen', 'location': 'Golden Gate Park', 'start': '11:30', 'end': '21:45', 'duration': 120},
        {'name': 'Sandra', 'location': 'Richmond District', 'start': '8:00', 'end': '15:15', 'duration': 30},
        {'name': 'Mary', 'location': 'Embarcadero', 'start': '16:45', 'end': '18:45', 'duration': 120},
        {'name': 'Deborah', 'location': 'Financial District', 'start': '19:00', 'end': '20:45', 'duration': 105},
        {'name': 'Elizabeth', 'location': 'Marina District', 'start': '8:30', 'end': '13:15', 'duration': 105}
    ]

    current_location = 'Mission District'
    current_time = parse_time('9:00')
    itinerary = []

    # Helper function to find next friend to meet
    def get_next_friend(current_loc, current_t, remaining_friends):
        for friend in remaining_friends:
            friend_start = parse_time(friend['start'])
            friend_end = parse_time(friend['end'])
            travel_time = travel_times[current_loc][friend['location']]
            arrival_time = current_t + timedelta(minutes=travel_time)
            
            # Check if we can meet this friend
            if arrival_time < friend_end:
                meet_start = max(arrival_time, friend_start)
                meet_end = meet_start + timedelta(minutes=friend['duration'])
                if meet_end <= friend_end:
                    return friend, meet_start, meet_end
        return None, None, None

    remaining_friends = friends.copy()
    while remaining_friends:
        friend, meet_start, meet_end = get_next_friend(current_location, current_time, remaining_friends)
        if not friend:
            break
        
        # Add travel to itinerary
        if current_location != friend['location']:
            travel_duration = travel_times[current_location][friend['location']]
            travel_start = current_time
            travel_end = current_time + timedelta(minutes=travel_duration)
            itinerary.append({
                'action': 'travel',
                'from': current_location,
                'to': friend['location'],
                'start_time': format_time(travel_start),
                'end_time': format_time(travel_end)
            })
        
        # Add meeting to itinerary
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': format_time(meet_start),
            'end_time': format_time(meet_end)
        })
        
        # Update current state
        current_location = friend['location']
        current_time = meet_end
        remaining_friends.remove(friend)

    # Filter out only meet actions for final output
    meet_entries = [entry for entry in itinerary if entry['action'] == 'meet']
    return {'itinerary': meet_entries}

schedule = calculate_schedule()
print(json.dumps(schedule, indent=2))