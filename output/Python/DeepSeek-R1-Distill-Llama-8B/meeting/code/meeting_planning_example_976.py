from datetime import time, timedelta

# Define travel distances between locations
distance = {
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Fisherman's Wharf'): 6,
    ('Embarcadero', 'Marina District'): 12,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'Presidio'): 32,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'North Beach'): 22,
    ('Bayview', 'Fisherman's Wharf'): 25,
    ('Bayview', 'Marina District'): 27,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Bayview'): 20,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Fisherman's Wharf'): 8,
    ('Chinatown', 'Marina District'): 12,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Fisherman's Wharf'): 19,
    ('Alamo Square', 'Marina District'): 15,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Fisherman's Wharf'): 10,
    ('Nob Hill', 'Marina District'): 11,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Fisherman's Wharf'): 19,
    ('Presidio', 'Marina District'): 11,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Fisherman's Wharf'): 15,
    ('Union Square', 'Marina District'): 18,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Fisherman's Wharf'): 24,
    ('The Castro', 'Marina District'): 21,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Bayview'): 25,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'The Castro'): 23,
    ('North Beach', 'Fisherman's Wharf'): 5,
    ('North Beach', 'Marina District'): 9,
    ('Fisherman's Wharf', 'Embarcadero'): 8,
    ('Fisherman's Wharf', 'Bayview'): 26,
    ('Fisherman's Wharf', 'Chinatown'): 12,
    ('Fisherman's Wharf', 'Alamo Square'): 21,
    ('Fisherman's Wharf', 'Nob Hill'): 11,
    ('Fisherman's Wharf', 'Presidio'): 17,
    ('Fisherman's Wharf', 'Union Square'): 13,
    ('Fisherman's Wharf', 'The Castro'): 27,
    ('Fisherman's Wharf', 'North Beach'): 6,
    ('Fisherman's Wharf', 'Marina District'): 9,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Fisherman's Wharf'): 10,
}

itinerary = []

# Try meeting each friend starting with the earliest availability
friends = [
    {'name': 'Stephanie', 'location': 'The Castro', 'availability_start': time(7, 30), 'availability_end': time(10, 15), 'duration': 60},
    {'name': 'Thomas', 'location': 'Fisherman's Wharf', 'availability_start': time(13, 30), 'availability_end': time(19, 0), 'duration': 30},
    {'name': 'Nancy', 'location': 'North Beach', 'availability_start': time(14, 45), 'availability_end': time(20, 0), 'duration': 15},
    {'name': 'Jessica', 'location': 'Nob Hill', 'availability_start': time(16, 30), 'availability_end': time(18, 45), 'duration': 120},
    {'name': 'Karen', 'location': 'Chinatown', 'availability_start': time(19, 15), 'availability_end': time(21, 15), 'duration': 90},
    {'name': 'Sarah', 'location': 'Alamo Square', 'availability_start': time(20, 0), 'availability_end': time(21, 45), 'duration': 105},
    {'name': 'Matthew', 'location': 'Bayview', 'availability_start': time(19, 0), 'availability_end': time(22, 0), 'duration': 120},
    {'name': 'Mary', 'location': 'Union Square', 'availability_start': time(16, 45), 'availability_end': time(21, 30), 'duration': 60},
    {'name': 'Charles', 'location': 'The Castro', 'availability_start': time(16, 30), 'availability_end': time(22, 0), 'duration': 105},
    {'name': 'Brian', 'location': 'Marina District', 'availability_start': time(12, 15), 'availability_end': time(18, 0), 'duration': 60},
]

for friend in friends:
    start_time = friend['availability_start']
    end_time = friend['availability_end']
    required_duration = friend['duration']
    latest_start = end_time - timedelta(minutes=required_duration)
    earliest_start = start_time

    # Calculate possible start times
    possible_start_times = []
    for hour in range(start_time.hour, latest_start.hour + 1):
        for minute in range(0, 60, 15):
            possible_start = time(hour, minute)
            if possible_start < earliest_start:
                continue
            possible_start_times.append(possible_start)

    # Try to meet this friend
    for possible_start in possible_start_times:
        # Calculate arrival and departure times
        travel_time = distance[('Embarcadero', friend['location'])]
        arrival_time = possible_start + timedelta(minutes=travel_time)
        departure_time = arrival_time + timedelta(minutes=required_duration)

        # Check if arrival and departure fit within the friend's availability
        if arrival_time < friend['availability_start'] or departure_time > friend['availability_end']:
            continue

        # Add the meeting to the itinerary
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': possible_start.strftime("%H:%M"),
            'end_time': departure_time.strftime("%H:%M")
        })

        # Update current time to departure_time
        current_time = departure_time

        # Try to meet next friends after the current_time
        for next_friend in friends:
            if next_friend == friend:
                continue
            next_start = current_time + timedelta(minutes=1)
            while next_start <= current_time:
                next_start = current_time + timedelta(minutes=1)
            if next_start > friend['availability_end']:
                break
            # Calculate possible start times for next friend
            next_possible_start_times = []
            for hour in range(next_start.hour, friend['availability_end'].hour + 1):
                for minute in range(0, 60, 15):
                    next_possible_start = time(hour, minute)
                    if next_possible_start < next_start:
                        continue
                    next_possible_start_times.append(next_possible_start)
            # Try each possible start time for next friend
            for next_possible_start in next_possible_start_times:
                next_travel_time = distance[('Embarcadero', next_friend['location'])]
                next_arrival_time = next_possible_start + timedelta(minutes=next_travel_time)
                next_departure_time = next_arrival_time + timedelta(minutes=next_friend['duration'])
                if next_arrival_time < next_start or next_departure_time > friend['availability_end']:
                    continue
                itinerary.append({
                    'action': 'meet',
                    'location': next_friend['location'],
                    'person': next_friend['name'],
                    'start_time': next_possible_start.strftime("%H:%M"),
                    'end_time': next_departure_time.strftime("%H:%M")
                })
                current_time = next_departure_time
                break
            else:
                continue
            break
        else:
            continue
        break
    else:
        continue
    break

itinerary_dict = {
    "itinerary": []
}
for item in itinerary:
    start = item['start_time']
    end = item['end_time']
    location = item['location']
    person = item['person']
    itinerary_dict["itinerary"].append({
        "action": "meet",
        "location": location,
        "person": person,
        "start_time": start,
        "end_time": end
    })

print(json.dumps(itinerary_dict))