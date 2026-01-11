import json
from datetime import datetime, timedelta

# Define travel times as a dictionary of dictionaries
travel_times = {
    'Nob Hill': {'Presidio': 17, 'North Beach': 8, 'Fisherman\'s Wharf': 11, 'Pacific Heights': 8},
    'Presidio': {'Nob Hill': 18, 'North Beach': 17, 'Fisherman\'s Wharf': 19, 'Pacific Heights': 11},
    'North Beach': {'Nob Hill': 7, 'Presidio': 17, 'Fisherman\'s Wharf': 5, 'Pacific Heights': 8},
    'Fisherman\'s Wharf': {'Nob Hill': 11, 'Presidio': 17, 'North Beach': 6, 'Pacific Heights': 12},
    'Pacific Heights': {'Nob Hill': 8, 'Presidio': 11, 'North Beach': 9, 'Fisherman\'s Wharf': 13}
}

# Define constraints
constraints = {
    'Jeffrey': {'location': 'Presidio', 'available_from': '8:00', 'available_to': '10:00', 'min_duration': 105},
    'Steven': {'location': 'North Beach', 'available_from': '13:30', 'available_to': '22:00', 'min_duration': 45},
    'Barbara': {'location': 'Fisherman\'s Wharf', 'available_from': '18:00', 'available_to': '21:30', 'min_duration': 30},
    'John': {'location': 'Pacific Heights', 'available_from': '9:00', 'available_to': '13:30', 'min_duration': 15}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time_obj, minutes):
    return time_obj + timedelta(minutes=minutes)

def is_within(time_obj, start_time, end_time):
    return start_time <= time_obj <= end_time

def generate_possible_meetings(constraints):
    possible_meetings = []
    for person, details in constraints.items():
        start_time = parse_time(details['available_from'])
        end_time = parse_time(details['available_to'])
        min_duration = details['min_duration']
        location = details['location']
        current_time = start_time
        while current_time + timedelta(minutes=min_duration) <= end_time:
            possible_meetings.append({
                'location': location,
                'person': person,
                'start_time': current_time.strftime('%H:%M'),
                'end_time': (current_time + timedelta(minutes=min_duration)).strftime('%H:%M')
            })
            current_time += timedelta(minutes=1)  # Increment by 1 minute to explore all possibilities
    return possible_meetings

def calculate_travel_time(start_location, end_location):
    return travel_times[start_location][end_location]

def generate_itineraries(possible_meetings, start_location='Nob Hill', start_time='9:00'):
    start_time_obj = parse_time(start_time)
    itineraries = []

    def backtrack(current_location, current_time, visited, itinerary):
        if len(visited) == len(constraints):
            itineraries.append(itinerary[:])
            return
        
        for meeting in possible_meetings:
            if meeting['person'] not in visited:
                travel_time = calculate_travel_time(current_location, meeting['location'])
                new_start_time = add_minutes(current_time, travel_time)
                if is_within(new_start_time, parse_time(meeting['start_time']), parse_time(meeting['end_time'])):
                    itinerary.append({
                        'action': 'travel',
                        'location': meeting['location'],
                        'start_time': current_time.strftime('%H:%M'),
                        'end_time': new_start_time.strftime('%H:%M')
                    })
                    itinerary.append({
                        'action': 'meet',
                        'location': meeting['location'],
                        'person': meeting['person'],
                        'start_time': meeting['start_time'],
                        'end_time': meeting['end_time']
                    })
                    backtrack(meeting['location'], add_minutes(new_start_time, meeting['min_duration']), visited | {meeting['person']}, itinerary)
                    itinerary.pop()
                    itinerary.pop()

    backtrack(start_location, start_time_obj, set(), [])
    return itineraries

def find_optimal_itinerary(itineraries):
    max_meetings = 0
    optimal_itinerary = None
    for itinerary in itineraries:
        num_meetings = sum(1 for action in itinerary if action['action'] == 'meet')
        if num_meetings > max_meetings:
            max_meetings = num_meetings
            optimal_itinerary = itinerary
    return optimal_itinerary

def main():
    possible_meetings = generate_possible_meetings(constraints)
    itineraries = generate_itineraries(possible_meetings)
    optimal_itinerary = find_optimal_itinerary(itineraries)
    filtered_itinerary = [action for action in optimal_itinerary if action['action'] == 'meet']
    print(json.dumps({"itinerary": filtered_itinerary}, indent=2))

if __name__ == "__main__":
    main()