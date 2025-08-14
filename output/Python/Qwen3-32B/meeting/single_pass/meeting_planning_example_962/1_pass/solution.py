import heapq
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define travel times between locations
travel_times = {
    'The Castro': {
        'Marina District': 21,
        'Presidio': 20,
        'North Beach': 20,
        'Embarcadero': 22,
        'Haight-Ashbury': 6,
        'Golden Gate Park': 11,
        'Richmond District': 16,
        'Alamo Square': 8,
        'Financial District': 21,
        'Sunset District': 17,
    },
    'Marina District': {
        'The Castro': 22,
        'Presidio': 10,
        'North Beach': 11,
        'Embarcadero': 14,
        'Haight-Ashbury': 16,
        'Golden Gate Park': 18,
        'Richmond District': 11,
        'Alamo Square': 15,
        'Financial District': 17,
        'Sunset District': 19,
    },
    'Presidio': {
        'The Castro': 21,
        'Marina District': 11,
        'North Beach': 18,
        'Embarcadero': 20,
        'Haight-Ashbury': 15,
        'Golden Gate Park': 12,
        'Richmond District': 7,
        'Alamo Square': 19,
        'Financial District': 23,
        'Sunset District': 15,
    },
    'North Beach': {
        'The Castro': 23,
        'Marina District': 9,
        'Presidio': 17,
        'Embarcadero': 6,
        'Haight-Ashbury': 18,
        'Golden Gate Park': 22,
        'Richmond District': 18,
        'Alamo Square': 16,
        'Financial District': 8,
        'Sunset District': 27,
    },
    'Embarcadero': {
        'The Castro': 25,
        'Marina District': 12,
        'Presidio': 20,
        'North Beach': 5,
        'Haight-Ashbury': 21,
        'Golden Gate Park': 25,
        'Richmond District': 21,
        'Alamo Square': 19,
        'Financial District': 5,
        'Sunset District': 30,
    },
    'Haight-Ashbury': {
        'The Castro': 6,
        'Marina District': 17,
        'Presidio': 15,
        'North Beach': 19,
        'Embarcadero': 20,
        'Golden Gate Park': 7,
        'Richmond District': 10,
        'Alamo Square': 5,
        'Financial District': 21,
        'Sunset District': 15,
    },
    'Golden Gate Park': {
        'The Castro': 13,
        'Marina District': 16,
        'Presidio': 11,
        'North Beach': 23,
        'Embarcadero': 25,
        'Haight-Ashbury': 7,
        'Richmond District': 7,
        'Alamo Square': 9,
        'Financial District': 26,
        'Sunset District': 10,
    },
    'Richmond District': {
        'The Castro': 16,
        'Marina District': 9,
        'Presidio': 7,
        'North Beach': 17,
        'Embarcadero': 19,
        'Haight-Ashbury': 10,
        'Golden Gate Park': 9,
        'Alamo Square': 13,
        'Financial District': 22,
        'Sunset District': 11,
    },
    'Alamo Square': {
        'The Castro': 8,
        'Marina District': 15,
        'Presidio': 17,
        'North Beach': 15,
        'Embarcadero': 16,
        'Haight-Ashbury': 5,
        'Golden Gate Park': 9,
        'Richmond District': 11,
        'Financial District': 17,
        'Sunset District': 16,
    },
    'Financial District': {
        'The Castro': 20,
        'Marina District': 15,
        'Presidio': 22,
        'North Beach': 7,
        'Embarcadero': 4,
        'Haight-Ashbury': 19,
        'Golden Gate Park': 23,
        'Richmond District': 21,
        'Alamo Square': 17,
        'Sunset District': 30,
    },
    'Sunset District': {
        'The Castro': 17,
        'Marina District': 21,
        'Presidio': 16,
        'North Beach': 28,
        'Embarcadero': 30,
        'Haight-Ashbury': 15,
        'Golden Gate Park': 11,
        'Richmond District': 12,
        'Alamo Square': 17,
        'Financial District': 30,
    },
}

# Define friends and their constraints
friends = [
    {
        'name': 'Elizabeth',
        'location': 'Marina District',
        'start': 19 * 60 + 0,  # 7:00 PM
        'end': 20 * 60 + 45,   # 8:45 PM
        'duration': 105
    },
    {
        'name': 'Joshua',
        'location': 'Presidio',
        'start': 8 * 60 + 30,   # 8:30 AM
        'end': 13 * 60 + 15,    # 1:15 PM
        'duration': 105
    },
    {
        'name': 'Timothy',
        'location': 'North Beach',
        'start': 19 * 60 + 45,  # 7:45 PM
        'end': 22 * 60 + 0,     # 10:00 PM
        'duration': 90
    },
    {
        'name': 'David',
        'location': 'Embarcadero',
        'start': 10 * 60 + 45,  # 10:45 AM
        'end': 12 * 60 + 30,    # 12:30 PM
        'duration': 30
    },
    {
        'name': 'Kimberly',
        'location': 'Haight-Ashbury',
        'start': 16 * 60 + 45,  # 4:45 PM
        'end': 21 * 60 + 30,    # 9:30 PM
        'duration': 75
    },
    {
        'name': 'Lisa',
        'location': 'Golden Gate Park',
        'start': 17 * 60 + 30,  # 5:30 PM
        'end': 21 * 60 + 45,    # 9:45 PM
        'duration': 45
    },
    {
        'name': 'Stephanie',
        'location': 'Alamo Square',
        'start': 15 * 60 + 30,  # 3:30 PM
        'end': 16 * 60 + 30,    # 4:30 PM
        'duration': 30
    },
    {
        'name': 'Helen',
        'location': 'Financial District',
        'start': 17 * 60 + 30,  # 5:30 PM
        'end': 18 * 60 + 30,    # 6:30 PM
        'duration': 45
    },
    {
        'name': 'Laura',
        'location': 'Sunset District',
        'start': 17 * 60 + 45,  # 5:45 PM
        'end': 21 * 60 + 15,    # 9:15 PM
        'duration': 90
    }
]

# Precompute latest arrival for each friend
for friend in friends:
    friend['latest_arrival'] = friend['end'] - friend['duration']

# Assign indices to friends
friend_indices = {friend['name']: idx for idx, friend in enumerate(friends)}

# Initial state: current_time=9:00 AM (540), current_location='The Castro', met=0 (bitmask 0)
initial_time = 9 * 60
initial_location = 'The Castro'
initial_met = 0
initial_itinerary = []

# Priority queue: (-num_met, current_time, current_location, met_bitmask, itinerary)
heap = []
heapq.heappush(heap, (0, initial_time, initial_location, initial_met, initial_itinerary))

# Visited set: (location, met_bitmask) -> earliest_time
visited = {}

best_itinerary = []

# Process the priority queue
while heap:
    neg_num_met, current_time, current_location, met_bitmask, itinerary = heapq.heappop(heap)
    num_met = -neg_num_met

    # Check if this state is already processed with a better time
    key = (current_location, met_bitmask)
    if key in visited:
        if visited[key] <= current_time:
            continue
    visited[key] = current_time

    # Update best itinerary if this one has more friends met
    if len(itinerary) > len(best_itinerary):
        best_itinerary = itinerary.copy()

    # Try to meet each friend not yet met
    for idx, friend in enumerate(friends):
        if not (met_bitmask & (1 << idx)):
            # Friend not met yet
            friend_loc = friend['location']
            start = friend['start']
            latest_arrival = friend['latest_arrival']
            duration = friend['duration']

            # Get travel time from current_location to friend_loc
            if current_location not in travel_times or friend_loc not in travel_times[current_location]:
                continue
            travel_time = travel_times[current_location][friend_loc]

            arrival_time = current_time + travel_time

            # Check if arrival_time is within [start, latest_arrival]
            if start <= arrival_time <= latest_arrival:
                # Can meet this friend
                new_time = arrival_time + duration
                new_met_bitmask = met_bitmask | (1 << idx)
                new_itinerary = itinerary + [{
                    'action': 'meet',
                    'location': friend_loc,
                    'person': friend['name'],
                    'start_time': minutes_to_time_str(arrival_time),
                    'end_time': minutes_to_time_str(new_time)
                }]

                # Check if this new state is worth adding to the queue
                new_key = (friend_loc, new_met_bitmask)
                if new_key not in visited or new_time < visited[new_key]:
                    # Add to heap with priority - (num_met + 1)
                    heapq.heappush(heap, (
                        -(num_met + 1),
                        new_time,
                        friend_loc,
                        new_met_bitmask,
                        new_itinerary
                    ))

# Output the best itinerary as JSON
result = {
    "itinerary": best_itinerary
}
print(json.dumps(result, indent=2))