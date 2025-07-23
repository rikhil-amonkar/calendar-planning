import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def calculate_schedule():
    # Travel times in minutes (from -> to)
    travel_times = {
        'Russian Hill': {
            'Nob Hill': 5,
            'Mission District': 16,
            'Embarcadero': 8
        },
        'Nob Hill': {
            'Russian Hill': 5,
            'Mission District': 13,
            'Embarcadero': 9
        },
        'Mission District': {
            'Russian Hill': 15,
            'Nob Hill': 12,
            'Embarcadero': 19
        },
        'Embarcadero': {
            'Russian Hill': 8,
            'Nob Hill': 10,
            'Mission District': 20
        }
    }

    # Constraints
    arrival_time = time_to_minutes("9:00")
    friends = {
        'Patricia': {
            'location': 'Nob Hill',
            'window_start': time_to_minutes("18:30"),
            'window_end': time_to_minutes("21:45"),
            'duration': 90
        },
        'Ashley': {
            'location': 'Mission District',
            'window_start': time_to_minutes("20:30"),
            'window_end': time_to_minutes("21:15"),
            'duration': 45
        },
        'Timothy': {
            'location': 'Embarcadero',
            'window_start': time_to_minutes("9:45"),
            'window_end': time_to_minutes("17:45"),
            'duration': 120
        }
    }

    best_schedule = None
    max_meetings = 0

    # Try all possible meeting orders
    for order in permutations(['Patricia', 'Ashley', 'Timothy']):
        current_location = 'Russian Hill'
        current_time = arrival_time
        schedule = []
        meetings = 0

        for person in order:
            friend = friends[person]
            location = friend['location']
            travel_time = travel_times[current_location][location]
            arrival_at_location = current_time + travel_time

            # Calculate possible meeting window
            window_start = max(arrival_at_location, friend['window_start'])
            window_end = friend['window_end']
            available_time = window_end - window_start

            if available_time >= friend['duration']:
                meeting_start = window_start
                meeting_end = meeting_start + friend['duration']
                schedule.append({
                    'action': 'meet',
                    'location': location,
                    'person': person,
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                current_time = meeting_end
                current_location = location
                meetings += 1
            else:
                break

        if meetings > max_meetings or (meetings == max_meetings and best_schedule is None):
            max_meetings = meetings
            best_schedule = schedule

    return {'itinerary': best_schedule}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))