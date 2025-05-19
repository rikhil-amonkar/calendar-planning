import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def calculate_schedule():
    # Define travel times as a dictionary of dictionaries
    travel_times = {
        'Alamo Square': {
            'Russian Hill': 13,
            'Presidio': 18,
            'Chinatown': 16,
            'Sunset District': 16,
            'The Castro': 8,
            'Embarcadero': 17,
            'Golden Gate Park': 9
        },
        'Russian Hill': {
            'Alamo Square': 15,
            'Presidio': 14,
            'Chinatown': 9,
            'Sunset District': 23,
            'The Castro': 21,
            'Embarcadero': 8,
            'Golden Gate Park': 21
        },
        'Presidio': {
            'Alamo Square': 18,
            'Russian Hill': 14,
            'Chinatown': 21,
            'Sunset District': 15,
            'The Castro': 21,
            'Embarcadero': 20,
            'Golden Gate Park': 12
        },
        'Chinatown': {
            'Alamo Square': 17,
            'Russian Hill': 7,
            'Presidio': 19,
            'Sunset District': 29,
            'The Castro': 22,
            'Embarcadero': 5,
            'Golden Gate Park': 23
        },
        'Sunset District': {
            'Alamo Square': 17,
            'Russian Hill': 24,
            'Presidio': 16,
            'Chinatown': 30,
            'The Castro': 17,
            'Embarcadero': 31,
            'Golden Gate Park': 11
        },
        'The Castro': {
            'Alamo Square': 8,
            'Russian Hill': 18,
            'Presidio': 20,
            'Chinatown': 20,
            'Sunset District': 17,
            'Embarcadero': 22,
            'Golden Gate Park': 11
        },
        'Embarcadero': {
            'Alamo Square': 19,
            'Russian Hill': 8,
            'Presidio': 20,
            'Chinatown': 7,
            'Sunset District': 30,
            'The Castro': 25,
            'Golden Gate Park': 25
        },
        'Golden Gate Park': {
            'Alamo Square': 10,
            'Russian Hill': 19,
            'Presidio': 11,
            'Chinatown': 23,
            'Sunset District': 10,
            'The Castro': 13,
            'Embarcadero': 25
        }
    }

    # Define friends' availability and meeting requirements
    friends = {
        'Emily': {
            'location': 'Russian Hill',
            'start': '12:15',
            'end': '14:15',
            'duration': 105
        },
        'Mark': {
            'location': 'Presidio',
            'start': '14:45',
            'end': '19:30',
            'duration': 60
        },
        'Deborah': {
            'location': 'Chinatown',
            'start': '7:30',
            'end': '15:30',
            'duration': 45
        },
        'Margaret': {
            'location': 'Sunset District',
            'start': '21:30',
            'end': '22:30',
            'duration': 60
        },
        'George': {
            'location': 'The Castro',
            'start': '7:30',
            'end': '14:15',
            'duration': 60
        },
        'Andrew': {
            'location': 'Embarcadero',
            'start': '20:15',
            'end': '22:00',
            'duration': 75
        },
        'Steven': {
            'location': 'Golden Gate Park',
            'start': '11:15',
            'end': '21:15',
            'duration': 105
        }
    }

    # Initial state
    current_location = 'Alamo Square'
    current_time = time_to_minutes('9:00')
    itinerary = []

    # We'll try to meet friends in different orders to find the best schedule
    friend_names = ['Deborah', 'George', 'Steven', 'Emily', 'Mark', 'Andrew', 'Margaret']
    best_itinerary = None
    best_meetings = 0

    # Try all possible orders (permutations) of meeting friends
    for order in permutations(friend_names):
        temp_itinerary = []
        temp_location = current_location
        temp_time = current_time
        meetings = 0

        for name in order:
            friend = friends[name]
            location = friend['location']
            start_window = time_to_minutes(friend['start'])
            end_window = time_to_minutes(friend['end'])
            duration = friend['duration']

            # Calculate travel time
            travel_time = travel_times[temp_location][location]

            # Earliest we can arrive at location
            arrival_time = temp_time + travel_time

            # Check if we can meet within the friend's window
            meeting_start = max(arrival_time, start_window)
            meeting_end = meeting_start + duration

            if meeting_end <= end_window:
                # Add meeting to itinerary
                temp_itinerary.append({
                    'action': 'meet',
                    'location': location,
                    'person': name,
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                meetings += 1
                temp_location = location
                temp_time = meeting_end

        # Check if this order is better than previous best
        if meetings > best_meetings:
            best_meetings = meetings
            best_itinerary = temp_itinerary
        elif meetings == best_meetings and best_itinerary is None:
            best_itinerary = temp_itinerary

    # After trying all orders, return the best itinerary found
    return {'itinerary': best_itinerary}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))