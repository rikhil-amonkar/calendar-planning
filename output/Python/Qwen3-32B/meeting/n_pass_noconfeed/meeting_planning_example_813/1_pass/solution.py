import json

friends = [
    {
        'name': 'Joshua',
        'location': 'Embarcadero',
        'available_start': 585,  # 9:45 AM
        'available_end': 1080,   # 6:00 PM
        'required_duration': 105
    },
    {
        'name': 'Jeffrey',
        'location': 'Bayview',
        'available_start': 585,  # 9:45 AM
        'available_end': 1275,   # 8:15 PM
        'required_duration': 75
    },
    {
        'name': 'Charles',
        'location': 'Union Square',
        'available_start': 645,  # 10:45 AM
        'available_end': 1215,   # 8:15 PM
        'required_duration': 120
    },
    {
        'name': 'Joseph',
        'location': 'Chinatown',
        'available_start': 420,  # 7:00 AM
        'available_end': 930,    # 3:30 PM
        'required_duration': 60
    },
    {
        'name': 'Elizabeth',
        'location': 'Sunset District',
        'available_start': 540,  # 9:00 AM
        'available_end': 585,    # 9:45 AM
        'required_duration': 45
    },
    {
        'name': 'Matthew',
        'location': 'Golden Gate Park',
        'available_start': 660,  # 11:00 AM
        'available_end': 1170,   # 7:30 PM
        'required_duration': 45
    },
    {
        'name': 'Carol',
        'location': 'Financial District',
        'available_start': 645,  # 10:45 AM
        'available_end': 675,    # 11:15 AM
        'required_duration': 15
    },
    {
        'name': 'Paul',
        'location': 'Haight-Ashbury',
        'available_start': 1155, # 7:15 PM
        'available_end': 1230,   # 8:30 PM
        'required_duration': 15
    },
    {
        'name': 'Rebecca',
        'location': 'Mission District',
        'available_start': 1020, # 5:00 PM
        'available_end': 1425,   # 9:45 PM
        'required_duration': 45
    }
]

travel_times = {
    'Marina District': {
        'Embarcadero': 14,
        'Bayview': 27,
        'Union Square': 16,
        'Chinatown': 15,
        'Sunset District': 19,
        'Golden Gate Park': 18,
        'Financial District': 17,
        'Haight-Ashbury': 16,
        'Mission District': 20
    },
    'Embarcadero': {
        'Marina District': 12,
        'Bayview': 21,
        'Union Square': 10,
        'Chinatown': 7,
        'Sunset District': 30,
        'Golden Gate Park': 25,
        'Financial District': 5,
        'Haight-Ashbury': 21,
        'Mission District': 20
    },
    'Bayview': {
        'Marina District': 27,
        'Embarcadero': 19,
        'Union Square': 18,
        'Chinatown': 19,
        'Sunset District': 23,
        'Golden Gate Park': 22,
        'Financial District': 19,
        'Haight-Ashbury': 19,
        'Mission District': 13
    },
    'Union Square': {
        'Marina District': 18,
        'Embarcadero': 11,
        'Bayview': 15,
        'Chinatown': 7,
        'Sunset District': 27,
        'Golden Gate Park': 22,
        'Financial District': 9,
        'Haight-Ashbury': 18,
        'Mission District': 14
    },
    'Chinatown': {
        'Marina District': 12,
        'Embarcadero': 5,
        'Bayview': 20,
        'Union Square': 7,
        'Sunset District': 29,
        'Golden Gate Park': 23,
        'Financial District': 5,
        'Haight-Ashbury': 19,
        'Mission District': 17
    },
    'Sunset District': {
        'Marina District': 21,
        'Embarcadero': 30,
        'Bayview': 22,
        'Union Square': 30,
        'Chinatown': 30,
        'Golden Gate Park': 11,
        'Financial District': 30,
        'Haight-Ashbury': 15,
        'Mission District': 25
    },
    'Golden Gate Park': {
        'Marina District': 16,
        'Embarcadero': 25,
        'Bayview': 23,
        'Union Square': 22,
        'Chinatown': 23,
        'Sunset District': 10,
        'Financial District': 26,
        'Haight-Ashbury': 7,
        'Mission District': 17
    },
    'Financial District': {
        'Marina District': 15,
        'Embarcadero': 4,
        'Bayview': 19,
        'Union Square': 9,
        'Chinatown': 5,
        'Sunset District': 30,
        'Golden Gate Park': 23,
        'Haight-Ashbury': 19,
        'Mission District': 17
    },
    'Haight-Ashbury': {
        'Marina District': 17,
        'Embarcadero': 20,
        'Bayview': 18,
        'Union Square': 19,
        'Chinatown': 19,
        'Sunset District': 15,
        'Golden Gate Park': 7,
        'Financial District': 21,
        'Mission District': 11
    },
    'Mission District': {
        'Marina District': 19,
        'Embarcadero': 19,
        'Bayview': 14,
        'Union Square': 15,
        'Chinatown': 16,
        'Sunset District': 24,
        'Golden Gate Park': 17,
        'Financial District': 15,
        'Haight-Ashbury': 12
    }
}

current_time = 9 * 60  # 9:00 AM in minutes
current_location = 'Marina District'
itinerary = []
remaining_friends = friends.copy()

while True:
    possible_next = []
    for friend in remaining_friends:
        if current_location not in travel_times or friend['location'] not in travel_times[current_location]:
            continue
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        earliest_start = max(arrival_time, friend['available_start'])
        meeting_end = earliest_start + friend['required_duration']
        if meeting_end <= friend['available_end']:
            possible_next.append( (friend, earliest_start, meeting_end) )
    
    if not possible_next:
        break
    
    # Sort by meeting end time
    possible_next.sort(key=lambda x: x[2])
    chosen_friend, start, end = possible_next[0]
    
    # Add to itinerary
    itinerary.append({
        'action': 'meet',
        'location': chosen_friend['location'],
        'person': chosen_friend['name'],
        'start_time': f"{start//60}:{start%60:02d}",
        'end_time': f"{end//60}:{end%60:02d}"
    })
    
    # Update current time and location
    current_time = end
    current_location = chosen_friend['location']
    
    # Remove from remaining
    remaining_friends.remove(chosen_friend)

# Output as JSON
result = {
    "itinerary": itinerary
}

print(json.dumps(result, indent=2))