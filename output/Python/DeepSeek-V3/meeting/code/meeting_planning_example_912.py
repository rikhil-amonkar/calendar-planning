import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    'Union Square': {
        'Presidio': 24, 'Alamo Square': 15, 'Marina District': 18, 'Financial District': 9,
        'Nob Hill': 9, 'Sunset District': 27, 'Chinatown': 7, 'Russian Hill': 13,
        'North Beach': 10, 'Haight-Ashbury': 18
    },
    'Presidio': {
        'Union Square': 22, 'Alamo Square': 19, 'Marina District': 11, 'Financial District': 23,
        'Nob Hill': 18, 'Sunset District': 15, 'Chinatown': 21, 'Russian Hill': 14,
        'North Beach': 18, 'Haight-Ashbury': 15
    },
    'Alamo Square': {
        'Union Square': 14, 'Presidio': 17, 'Marina District': 15, 'Financial District': 17,
        'Nob Hill': 11, 'Sunset District': 16, 'Chinatown': 15, 'Russian Hill': 13,
        'North Beach': 15, 'Haight-Ashbury': 5
    },
    'Marina District': {
        'Union Square': 16, 'Presidio': 10, 'Alamo Square': 15, 'Financial District': 17,
        'Nob Hill': 12, 'Sunset District': 19, 'Chinatown': 15, 'Russian Hill': 8,
        'North Beach': 11, 'Haight-Ashbury': 16
    },
    'Financial District': {
        'Union Square': 9, 'Presidio': 22, 'Alamo Square': 17, 'Marina District': 15,
        'Nob Hill': 8, 'Sunset District': 30, 'Chinatown': 5, 'Russian Hill': 11,
        'North Beach': 7, 'Haight-Ashbury': 19
    },
    'Nob Hill': {
        'Union Square': 7, 'Presidio': 17, 'Alamo Square': 11, 'Marina District': 11,
        'Financial District': 9, 'Sunset District': 24, 'Chinatown': 6, 'Russian Hill': 5,
        'North Beach': 8, 'Haight-Ashbury': 13
    },
    'Sunset District': {
        'Union Square': 30, 'Presidio': 16, 'Alamo Square': 17, 'Marina District': 21,
        'Financial District': 30, 'Nob Hill': 27, 'Chinatown': 30, 'Russian Hill': 24,
        'North Beach': 28, 'Haight-Ashbury': 15
    },
    'Chinatown': {
        'Union Square': 7, 'Presidio': 19, 'Alamo Square': 17, 'Marina District': 12,
        'Financial District': 5, 'Nob Hill': 9, 'Sunset District': 29, 'Russian Hill': 7,
        'North Beach': 3, 'Haight-Ashbury': 19
    },
    'Russian Hill': {
        'Union Square': 10, 'Presidio': 14, 'Alamo Square': 15, 'Marina District': 7,
        'Financial District': 11, 'Nob Hill': 5, 'Sunset District': 23, 'Chinatown': 9,
        'North Beach': 5, 'Haight-Ashbury': 17
    },
    'North Beach': {
        'Union Square': 7, 'Presidio': 17, 'Alamo Square': 16, 'Marina District': 9,
        'Financial District': 8, 'Nob Hill': 7, 'Sunset District': 27, 'Chinatown': 6,
        'Russian Hill': 4, 'Haight-Ashbury': 18
    },
    'Haight-Ashbury': {
        'Union Square': 19, 'Presidio': 15, 'Alamo Square': 5, 'Marina District': 17,
        'Financial District': 21, 'Nob Hill': 15, 'Sunset District': 15, 'Chinatown': 19,
        'Russian Hill': 17, 'North Beach': 19
    }
}

# Friend constraints
friends = [
    {'name': 'Kimberly', 'location': 'Presidio', 'start': 15.5, 'end': 16.0, 'duration': 0.25},
    {'name': 'Elizabeth', 'location': 'Alamo Square', 'start': 19.25, 'end': 20.25, 'duration': 0.25},
    {'name': 'Joshua', 'location': 'Marina District', 'start': 10.5, 'end': 14.25, 'duration': 0.75},
    {'name': 'Sandra', 'location': 'Financial District', 'start': 19.5, 'end': 20.25, 'duration': 0.75},
    {'name': 'Kenneth', 'location': 'Nob Hill', 'start': 12.75, 'end': 21.75, 'duration': 0.5},
    {'name': 'Betty', 'location': 'Sunset District', 'start': 14.0, 'end': 19.0, 'duration': 1.0},
    {'name': 'Deborah', 'location': 'Chinatown', 'start': 17.25, 'end': 20.5, 'duration': 0.25},
    {'name': 'Barbara', 'location': 'Russian Hill', 'start': 17.5, 'end': 21.25, 'duration': 2.0},
    {'name': 'Steven', 'location': 'North Beach', 'start': 17.75, 'end': 20.75, 'duration': 1.5},
    {'name': 'Daniel', 'location': 'Haight-Ashbury', 'start': 18.5, 'end': 18.75, 'duration': 0.25}
]

def time_to_float(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours + minutes / 60.0

def float_to_time(time_float):
    hours = int(time_float)
    minutes = int((time_float - hours) * 60)
    return f"{hours}:{minutes:02d}"

def get_travel_time(from_loc, to_loc):
    return travel_times[from_loc][to_loc] / 60.0

def is_schedule_valid(schedule):
    current_time = 9.0  # Start at Union Square at 9:00 AM
    current_location = 'Union Square'
    
    itinerary = []
    
    for friend in schedule:
        # Travel to friend's location
        travel_time = get_travel_time(current_location, friend['location'])
        arrival_time = current_time + travel_time
        
        # Check if we can meet during their available time
        meeting_start = max(arrival_time, friend['start'])
        meeting_end = meeting_start + friend['duration']
        
        if meeting_end > friend['end']:
            return None  # Can't meet for required duration
        
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': float_to_time(meeting_start),
            'end_time': float_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = friend['location']
    
    return itinerary

def evaluate_schedule(schedule):
    itinerary = is_schedule_valid(schedule)
    if itinerary is None:
        return -1
    return len(itinerary)  # Maximize number of meetings

def find_best_schedule():
    best_score = -1
    best_itinerary = []
    
    # We'll try permutations of the friends, but limit to a reasonable number
    # due to computational constraints (10! is too large)
    for _ in range(1000):
        import random
        sample = random.sample(friends, len(friends))
        score = evaluate_schedule(sample)
        if score > best_score:
            best_score = score
            best_itinerary = is_schedule_valid(sample)
    
    return best_itinerary

def main():
    itinerary = find_best_schedule()
    if not itinerary:
        print(json.dumps({"itinerary": []}))
        return
    
    # Convert to the required output format
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()