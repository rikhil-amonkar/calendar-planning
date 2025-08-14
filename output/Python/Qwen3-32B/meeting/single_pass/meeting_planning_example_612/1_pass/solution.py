import itertools
import json

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

friends = [
    {
        'name': 'Emily',
        'location': 'Russian Hill',
        'available_start': 12 * 60 + 15,  # 735
        'available_end': 14 * 60 + 15,    # 855
        'required_duration': 105,
    },
    {
        'name': 'Mark',
        'location': 'Presidio',
        'available_start': 14 * 60 + 45,  # 885
        'available_end': 19 * 60 + 30,    # 1170
        'required_duration': 60,
    },
    {
        'name': 'Deborah',
        'location': 'Chinatown',
        'available_start': 7 * 60 + 30,   # 450
        'available_end': 15 * 60 + 30,    # 930
        'required_duration': 45,
    },
    {
        'name': 'Margaret',
        'location': 'Sunset District',
        'available_start': 21 * 60 + 30,  # 1290
        'available_end': 22 * 60 + 30,    # 1350
        'required_duration': 60,
    },
    {
        'name': 'George',
        'location': 'The Castro',
        'available_start': 7 * 60 + 30,   # 450
        'available_end': 14 * 60 + 15,    # 855
        'required_duration': 60,
    },
    {
        'name': 'Andrew',
        'location': 'Embarcadero',
        'available_start': 20 * 60 + 15,  # 1215
        'available_end': 22 * 60 + 0,     # 1320
        'required_duration': 75,
    },
    {
        'name': 'Steven',
        'location': 'Golden Gate Park',
        'available_start': 11 * 60 + 15,  # 675
        'available_end': 21 * 60 + 15,    # 1275
        'required_duration': 105,
    },
]

travel_times = {
    'Alamo Square': {
        'Russian Hill': 13,
        'Presidio': 18,
        'Chinatown': 16,
        'Sunset District': 16,
        'The Castro': 8,
        'Embarcadero': 17,
        'Golden Gate Park': 9,
    },
    'Russian Hill': {
        'Alamo Square': 15,
        'Presidio': 14,
        'Chinatown': 9,
        'Sunset District': 23,
        'The Castro': 21,
        'Embarcadero': 8,
        'Golden Gate Park': 21,
    },
    'Presidio': {
        'Alamo Square': 18,
        'Russian Hill': 14,
        'Chinatown': 21,
        'Sunset District': 15,
        'The Castro': 21,
        'Embarcadero': 20,
        'Golden Gate Park': 12,
    },
    'Chinatown': {
        'Alamo Square': 17,
        'Russian Hill': 7,
        'Presidio': 19,
        'Sunset District': 29,
        'The Castro': 22,
        'Embarcadero': 5,
        'Golden Gate Park': 23,
    },
    'Sunset District': {
        'Alamo Square': 17,
        'Russian Hill': 24,
        'Presidio': 16,
        'Chinatown': 30,
        'The Castro': 17,
        'Embarcadero': 31,
        'Golden Gate Park': 11,
    },
    'The Castro': {
        'Alamo Square': 8,
        'Russian Hill': 18,
        'Presidio': 20,
        'Chinatown': 20,
        'Sunset District': 17,
        'Embarcadero': 22,
        'Golden Gate Park': 11,
    },
    'Embarcadero': {
        'Alamo Square': 19,
        'Russian Hill': 8,
        'Presidio': 20,
        'Chinatown': 7,
        'Sunset District': 30,
        'The Castro': 25,
        'Golden Gate Park': 25,
    },
    'Golden Gate Park': {
        'Alamo Square': 10,
        'Russian Hill': 19,
        'Presidio': 11,
        'Chinatown': 23,
        'Sunset District': 10,
        'The Castro': 13,
        'Embarcadero': 25,
    },
}

best_perm = None
max_len = 0

for r in range(1, len(friends) + 1):
    for perm in itertools.permutations(friends, r):
        current_time = 9 * 60  # 9:00 AM in minutes
        current_location = 'Alamo Square'
        valid = True
        for friend in perm:
            dest = friend['location']
            if current_location not in travel_times or dest not in travel_times[current_location]:
                valid = False
                break
            travel_time = travel_times[current_location][dest]
            arrival_time = current_time + travel_time
            available_start = friend['available_start']
            available_end = friend['available_end']
            required_duration = friend['required_duration']
            meeting_start = max(arrival_time, available_start)
            meeting_end = meeting_start + required_duration
            if meeting_end > available_end:
                valid = False
                break
            current_time = meeting_end
            current_location = dest
        if valid:
            if len(perm) > max_len:
                max_len = len(perm)
                best_perm = perm
            elif len(perm) == max_len:
                # Tie, keep the first one found
                pass

# Now generate the itinerary for best_perm
itinerary = []
if best_perm:
    current_time = 9 * 60
    current_location = 'Alamo Square'
    for friend in best_perm:
        dest = friend['location']
        travel_time = travel_times[current_location][dest]
        arrival_time = current_time + travel_time
        available_start = friend['available_start']
        available_end = friend['available_end']
        required_duration = friend['required_duration']
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + required_duration
        # Convert to time strings
        start_str = minutes_to_time(meeting_start)
        end_str = minutes_to_time(meeting_end)
        itinerary.append({
            "action": "meet",
            "location": dest,
            "person": friend['name'],
            "start_time": start_str,
            "end_time": end_str
        })
        current_time = meeting_end
        current_location = dest

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))