import itertools
import json

def time_str_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Define friends with their data
friends = [
    {
        'name': 'David',
        'location': 'Mission District',
        'available_start': '8:00',
        'available_end': '19:45',
        'meeting_duration': 45
    },
    {
        'name': 'Kenneth',
        'location': 'Alamo Square',
        'available_start': '14:00',
        'available_end': '19:45',
        'meeting_duration': 120
    },
    {
        'name': 'John',
        'location': 'Pacific Heights',
        'available_start': '17:00',
        'available_end': '20:00',
        'meeting_duration': 15
    },
    {
        'name': 'Charles',
        'location': 'Union Square',
        'available_start': '21:45',
        'available_end': '22:45',
        'meeting_duration': 60
    },
    {
        'name': 'Deborah',
        'location': 'Golden Gate Park',
        'available_start': '7:00',
        'available_end': '18:15',
        'meeting_duration': 90
    },
    {
        'name': 'Karen',
        'location': 'Sunset District',
        'available_start': '17:45',
        'available_end': '21:15',
        'meeting_duration': 15
    },
    {
        'name': 'Carol',
        'location': 'Presidio',
        'available_start': '8:15',
        'available_end': '9:15',
        'meeting_duration': 30
    }
]

# Preprocess available times into minutes
for f in friends:
    f['available_start_minutes'] = time_str_to_minutes(f['available_start'])
    f['available_end_minutes'] = time_str_to_minutes(f['available_end'])

# Define travel times between locations
travel_times = {
    'Chinatown': {
        'Mission District': 18,
        'Alamo Square': 17,
        'Pacific Heights': 10,
        'Union Square': 7,
        'Golden Gate Park': 23,
        'Sunset District': 29,
        'Presidio': 19
    },
    'Mission District': {
        'Chinatown': 16,
        'Alamo Square': 11,
        'Pacific Heights': 16,
        'Union Square': 15,
        'Golden Gate Park': 17,
        'Sunset District': 24,
        'Presidio': 25
    },
    'Alamo Square': {
        'Chinatown': 16,
        'Mission District': 10,
        'Pacific Heights': 10,
        'Union Square': 14,
        'Golden Gate Park': 9,
        'Sunset District': 16,
        'Presidio': 18
    },
    'Pacific Heights': {
        'Chinatown': 11,
        'Mission District': 15,
        'Alamo Square': 10,
        'Union Square': 12,
        'Golden Gate Park': 15,
        'Sunset District': 21,
        'Presidio': 11
    },
    'Union Square': {
        'Chinatown': 7,
        'Mission District': 14,
        'Alamo Square': 15,
        'Pacific Heights': 15,
        'Golden Gate Park': 22,
        'Sunset District': 26,
        'Presidio': 24
    },
    'Golden Gate Park': {
        'Chinatown': 23,
        'Mission District': 17,
        'Alamo Square': 10,
        'Pacific Heights': 16,
        'Union Square': 22,
        'Sunset District': 10,
        'Presidio': 11
    },
    'Sunset District': {
        'Chinatown': 30,
        'Mission District': 24,
        'Alamo Square': 17,
        'Pacific Heights': 21,
        'Union Square': 30,
        'Golden Gate Park': 11,
        'Presidio': 16
    },
    'Presidio': {
        'Chinatown': 21,
        'Mission District': 26,
        'Alamo Square': 18,
        'Pacific Heights': 11,
        'Union Square': 22,
        'Golden Gate Park': 12,
        'Sunset District': 15
    }
}

best_itinerary = []
max_length = 0

# Check all permutations from largest to smallest
for k in range(len(friends), 0, -1):
    for perm in itertools.permutations(friends, k):
        current_time = time_str_to_minutes('9:00')
        current_location = 'Chinatown'
        valid = True
        itinerary = []
        for friend in perm:
            dest = friend['location']
            if current_location not in travel_times or dest not in travel_times[current_location]:
                valid = False
                break
            travel_time = travel_times[current_location][dest]
            arrival_time = current_time + travel_time
            available_start = friend['available_start_minutes']
            available_end = friend['available_end_minutes']
            meeting_duration = friend['meeting_duration']
            
            # Check if arrival_time + meeting_duration fits into available time
            if arrival_time < available_start:
                start_time = available_start
                end_time = start_time + meeting_duration
                if end_time > available_end:
                    valid = False
                    break
                current_time = end_time
            elif arrival_time <= available_end:
                end_time = arrival_time + meeting_duration
                if end_time > available_end:
                    valid = False
                    break
                current_time = end_time
            else:
                valid = False
                break
            
            # Update current location
            current_location = dest
            # Record the itinerary entry
            itinerary.append({
                'action': 'meet',
                'location': dest,
                'person': friend['name'],
                'start_time': minutes_to_time_str(start_time if arrival_time < available_start else arrival_time),
                'end_time': minutes_to_time_str(current_time)
            })
        
        if valid:
            if len(itinerary) > max_length:
                max_length = len(itinerary)
                best_itinerary = itinerary
            elif len(itinerary) == max_length:
                # For ties, we can keep the first one found or compare which ends earliest, etc.
                # For simplicity, we'll just keep the first one found with max_length
                pass
    if max_length == k:
        # No need to check smaller subsets since we already found the maximum
        break

# Output the result as JSON
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))