import json
from datetime import datetime, timedelta

# Define the travel times
travel_times = {
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Richmond District'): 9,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Bayview'): 27,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Sunset District'): 12,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 25,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Sunset District'): 10,
}

# Define the meetings
meetings = {
    'Elizabeth': {'location': 'Mission District', 'start': '10:30', 'end': '20:00', 'min_duration': 90},
    'David': {'location': 'Union Square', 'start': '15:15', 'end': '19:00', 'min_duration': 45},
    'Sandra': {'location': 'Pacific Heights', 'start': '07:00', 'end': '20:00', 'min_duration': 120},
    'Thomas': {'location': 'Bayview', 'start': '19:30', 'end': '20:30', 'min_duration': 30},
    'Robert': {'location': 'Fisherman\'s Wharf', 'start': '10:00', 'end': '15:00', 'min_duration': 15},
    'Kenneth': {'location': 'Marina District', 'start': '10:45', 'end': '13:00', 'min_duration': 45},
    'Melissa': {'location': 'Richmond District', 'start': '18:15', 'end': '20:00', 'min_duration': 15},
    'Kimberly': {'location': 'Sunset District', 'start': '10:15', 'end': '18:15', 'min_duration': 105},
    'Amanda': {'location': 'Golden Gate Park', 'start': '07:45', 'end': '18:45', 'min_duration': 15},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def can_meet(start, end, min_duration):
    duration = (end - start).seconds // 60
    return duration >= min_duration

def find_optimal_schedule():
    start_time = parse_time('09:00')
    current_location = 'Haight-Ashbury'
    itinerary = []

    # Sort meetings by start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))

    for name, details in sorted_meetings:
        location = details['location']
        start = parse_time(details['start'])
        end = parse_time(details['end'])
        min_duration = details['min_duration']

        # Calculate travel time
        travel_time = travel_times.get((current_location, location), float('inf'))
        potential_start_time = start_time + timedelta(minutes=travel_time)

        # Adjust the start time to be within the person's availability
        if potential_start_time < start:
            meet_start = start
        else:
            meet_start = potential_start_time

        meet_end = meet_start + timedelta(minutes=min_duration)

        # Ensure the meeting fits within the available time
        if meet_start >= start and meet_end <= end:
            # Special check for Robert's meeting time
            if name == 'Robert' and (meet_start < parse_time('10:00') or meet_end > parse_time('15:00')):
                continue

            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": meet_start.strftime('%H:%M'),
                "end_time": meet_end.strftime('%H:%M')
            })
            start_time = meet_end
            current_location = location

    return itinerary

optimal_itinerary = find_optimal_schedule()
output = {"itinerary": optimal_itinerary}
print(json.dumps(output, indent=2))