import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input data
travel_times = {
    'Embarcadero': {
        'Golden Gate Park': 25,
        'Haight-Ashbury': 21,
        'Bayview': 21,
        'Presidio': 20,
        'Financial District': 5
    },
    'Golden Gate Park': {
        'Embarcadero': 25,
        'Haight-Ashbury': 7,
        'Bayview': 23,
        'Presidio': 11,
        'Financial District': 26
    },
    'Haight-Ashbury': {
        'Embarcadero': 20,
        'Golden Gate Park': 7,
        'Bayview': 18,
        'Presidio': 15,
        'Financial District': 21
    },
    'Bayview': {
        'Embarcadero': 19,
        'Golden Gate Park': 22,
        'Haight-Ashbury': 19,
        'Presidio': 31,
        'Financial District': 19
    },
    'Presidio': {
        'Embarcadero': 20,
        'Golden Gate Park': 12,
        'Haight-Ashbury': 15,
        'Bayview': 31,
        'Financial District': 23
    },
    'Financial District': {
        'Embarcadero': 4,
        'Golden Gate Park': 23,
        'Haight-Ashbury': 19,
        'Bayview': 19,
        'Presidio': 22
    }
}

friends = [
    {
        'name': 'Mary',
        'location': 'Golden Gate Park',
        'available_start': '8:45',
        'available_end': '11:45',
        'duration': 45
    },
    {
        'name': 'Kevin',
        'location': 'Haight-Ashbury',
        'available_start': '10:15',
        'available_end': '16:15',
        'duration': 90
    },
    {
        'name': 'Deborah',
        'location': 'Bayview',
        'available_start': '15:00',
        'available_end': '19:15',
        'duration': 120
    },
    {
        'name': 'Stephanie',
        'location': 'Presidio',
        'available_start': '10:00',
        'available_end': '17:15',
        'duration': 120
    },
    {
        'name': 'Emily',
        'location': 'Financial District',
        'available_start': '11:30',
        'available_end': '21:45',
        'duration': 105
    }
]

# Generate all possible orders to meet friends
def generate_schedules():
    possible_friends = [f for f in friends]
    return permutations(possible_friends)

def calculate_schedule_score(schedule):
    current_time = time_to_minutes('9:00')
    current_location = 'Embarcadero'
    total_meetings = 0
    itinerary = []
    
    for friend in schedule:
        # Calculate travel time
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        
        # Check if we can meet this friend
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        
        # Determine meeting window
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + friend['duration']
        
        if meeting_end > available_end:
            continue  # Can't meet this friend
        
        # Add to itinerary
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        total_meetings += 1
        current_time = meeting_end
        current_location = friend['location']
    
    return total_meetings, itinerary

def find_optimal_schedule():
    best_score = 0
    best_itinerary = []
    
    for schedule in generate_schedules():
        score, itinerary = calculate_schedule_score(schedule)
        if score > best_score:
            best_score = score
            best_itinerary = itinerary
    
    return best_itinerary

# Main execution
optimal_itinerary = find_optimal_schedule()
output = {
    "itinerary": optimal_itinerary
}
print(json.dumps(output, indent=2))