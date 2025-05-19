import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(dt):
    return dt.strftime('%-H:%M')

def main():
    # Travel times in minutes between locations
    travel_times = {
        'Fisherman\'s Wharf': {
            'Golden Gate Park': 25,
            'Presidio': 17,
            'Richmond District': 18
        },
        'Golden Gate Park': {
            'Fisherman\'s Wharf': 24,
            'Presidio': 11,
            'Richmond District': 7
        },
        'Presidio': {
            'Fisherman\'s Wharf': 19,
            'Golden Gate Park': 12,
            'Richmond District': 7
        },
        'Richmond District': {
            'Fisherman\'s Wharf': 18,
            'Golden Gate Park': 9,
            'Presidio': 7
        }
    }

    # Constraints
    current_location = 'Fisherman\'s Wharf'
    current_time = parse_time('9:00')
    
    friends = [
        {
            'name': 'Melissa',
            'location': 'Golden Gate Park',
            'available_start': parse_time('8:30'),
            'available_end': parse_time('20:00'),
            'min_duration': 15
        },
        {
            'name': 'Nancy',
            'location': 'Presidio',
            'available_start': parse_time('19:45'),
            'available_end': parse_time('22:00'),
            'min_duration': 105
        },
        {
            'name': 'Emily',
            'location': 'Richmond District',
            'available_start': parse_time('16:45'),
            'available_end': parse_time('22:00'),
            'min_duration': 120
        }
    ]

    itinerary = []

    # Try to meet Melissa first (earliest available)
    melissa = friends[0]
    travel_time = travel_times[current_location][melissa['location']]
    arrival_time = current_time + timedelta(minutes=travel_time)
    
    # Check if we can meet Melissa
    if arrival_time <= melissa['available_end']:
        start_time = max(arrival_time, melissa['available_start'])
        end_time = start_time + timedelta(minutes=melissa['min_duration'])
        if end_time <= melissa['available_end']:
            itinerary.append({
                'action': 'meet',
                'location': melissa['location'],
                'person': melissa['name'],
                'start_time': format_time(start_time),
                'end_time': format_time(end_time)
            })
            current_time = end_time
            current_location = melissa['location']

    # Now try to meet Emily (next earliest available)
    emily = friends[2]
    travel_time = travel_times[current_location][emily['location']]
    arrival_time = current_time + timedelta(minutes=travel_time)
    
    if arrival_time <= emily['available_end']:
        start_time = max(arrival_time, emily['available_start'])
        end_time = start_time + timedelta(minutes=emily['min_duration'])
        if end_time <= emily['available_end']:
            itinerary.append({
                'action': 'meet',
                'location': emily['location'],
                'person': emily['name'],
                'start_time': format_time(start_time),
                'end_time': format_time(end_time)
            })
            current_time = end_time
            current_location = emily['location']

    # Finally try to meet Nancy (latest available)
    nancy = friends[1]
    travel_time = travel_times[current_location][nancy['location']]
    arrival_time = current_time + timedelta(minutes=travel_time)
    
    if arrival_time <= nancy['available_end']:
        start_time = max(arrival_time, nancy['available_start'])
        end_time = start_time + timedelta(minutes=nancy['min_duration'])
        if end_time <= nancy['available_end']:
            itinerary.append({
                'action': 'meet',
                'location': nancy['location'],
                'person': nancy['name'],
                'start_time': format_time(start_time),
                'end_time': format_time(end_time)
            })

    # Output the itinerary
    print(json.dumps({'itinerary': itinerary}, indent=2))

if __name__ == '__main__':
    main()