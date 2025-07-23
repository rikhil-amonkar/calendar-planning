import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    'Russian Hill': {
        'Marina District': 7, 'Financial District': 11, 'Alamo Square': 15, 'Golden Gate Park': 21,
        'The Castro': 21, 'Bayview': 23, 'Sunset District': 23, 'Haight-Ashbury': 17, 'Nob Hill': 5
    },
    'Marina District': {
        'Russian Hill': 8, 'Financial District': 17, 'Alamo Square': 15, 'Golden Gate Park': 18,
        'The Castro': 22, 'Bayview': 27, 'Sunset District': 19, 'Haight-Ashbury': 16, 'Nob Hill': 12
    },
    'Financial District': {
        'Russian Hill': 11, 'Marina District': 15, 'Alamo Square': 17, 'Golden Gate Park': 23,
        'The Castro': 20, 'Bayview': 19, 'Sunset District': 30, 'Haight-Ashbury': 19, 'Nob Hill': 8
    },
    'Alamo Square': {
        'Russian Hill': 13, 'Marina District': 15, 'Financial District': 17, 'Golden Gate Park': 9,
        'The Castro': 8, 'Bayview': 16, 'Sunset District': 16, 'Haight-Ashbury': 5, 'Nob Hill': 11
    },
    'Golden Gate Park': {
        'Russian Hill': 19, 'Marina District': 16, 'Financial District': 26, 'Alamo Square': 9,
        'The Castro': 13, 'Bayview': 23, 'Sunset District': 10, 'Haight-Ashbury': 7, 'Nob Hill': 20
    },
    'The Castro': {
        'Russian Hill': 18, 'Marina District': 21, 'Financial District': 21, 'Alamo Square': 8,
        'Golden Gate Park': 11, 'Bayview': 19, 'Sunset District': 17, 'Haight-Ashbury': 6, 'Nob Hill': 16
    },
    'Bayview': {
        'Russian Hill': 23, 'Marina District': 27, 'Financial District': 19, 'Alamo Square': 16,
        'Golden Gate Park': 22, 'The Castro': 19, 'Sunset District': 23, 'Haight-Ashbury': 19, 'Nob Hill': 20
    },
    'Sunset District': {
        'Russian Hill': 24, 'Marina District': 21, 'Financial District': 30, 'Alamo Square': 17,
        'Golden Gate Park': 11, 'The Castro': 17, 'Bayview': 22, 'Haight-Ashbury': 15, 'Nob Hill': 27
    },
    'Haight-Ashbury': {
        'Russian Hill': 17, 'Marina District': 17, 'Financial District': 21, 'Alamo Square': 5,
        'Golden Gate Park': 7, 'The Castro': 6, 'Bayview': 18, 'Sunset District': 15, 'Nob Hill': 15
    },
    'Nob Hill': {
        'Russian Hill': 5, 'Marina District': 11, 'Financial District': 9, 'Alamo Square': 11,
        'Golden Gate Park': 17, 'The Castro': 17, 'Bayview': 19, 'Sunset District': 24, 'Haight-Ashbury': 13
    }
}

# Friend data: name -> (location, available_start, available_end, min_duration)
friends = {
    'Mark': ('Marina District', 18.75, 21.0, 1.5),
    'Karen': ('Financial District', 9.5, 12.75, 1.5),
    'Barbara': ('Alamo Square', 10.0, 19.5, 1.5),
    'Nancy': ('Golden Gate Park', 16.75, 20.0, 1.75),
    'David': ('The Castro', 9.0, 18.0, 2.0),
    'Linda': ('Bayview', 18.25, 19.75, 0.75),
    'Kevin': ('Sunset District', 10.0, 17.75, 2.0),
    'Matthew': ('Haight-Ashbury', 10.25, 15.5, 0.75),
    'Andrew': ('Nob Hill', 11.75, 16.75, 1.75)
}

def time_to_float(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours + minutes / 60.0

def float_to_time(time_float):
    hours = int(time_float)
    minutes = int((time_float - hours) * 60)
    return f"{hours}:{minutes:02d}"

def get_travel_time(from_loc, to_loc):
    if from_loc == to_loc:
        return 0
    try:
        return travel_times[from_loc][to_loc] / 60.0
    except KeyError:
        return travel_times[from_loc][to_loc.replace(' ', '')] / 60.0

def schedule_meeting(current_time, current_location, friend_name, friend_data):
    location, start, end, duration = friend_data
    travel_time = get_travel_time(current_location, location)
    
    # Earliest we can arrive
    arrival_time = current_time + travel_time
    meeting_start = max(arrival_time, start)
    
    if meeting_start + duration > end:
        return None  # Can't meet
    
    return {
        'action': 'meet',
        'location': location,
        'person': friend_name,
        'start_time': float_to_time(meeting_start),
        'end_time': float_to_time(meeting_start + duration)
    }, meeting_start + duration, location

def evaluate_schedule(order):
    current_time = 9.0  # Start at Russian Hill at 9:00
    current_location = 'Russian Hill'
    itinerary = []
    met_friends = set()
    
    for friend_name in order:
        if friend_name in friends:
            meeting = schedule_meeting(current_time, current_location, friend_name, friends[friend_name])
            if meeting is None:
                continue
            meeting_entry, new_time, new_location = meeting
            itinerary.append(meeting_entry)
            current_time = new_time
            current_location = new_location
            met_friends.add(friend_name)
    
    # Try to meet Mark at the end if we haven't already
    if 'Mark' not in met_friends:
        meeting = schedule_meeting(current_time, current_location, 'Mark', friends['Mark'])
        if meeting is not None:
            meeting_entry, new_time, new_location = meeting
            itinerary.append(meeting_entry)
            met_friends.add('Mark')
    
    return len(met_friends), itinerary

def find_optimal_schedule():
    best_count = 0
    best_itinerary = []
    
    # We'll try different orders, prioritizing friends with tighter time windows first
    friend_order = ['Karen', 'Matthew', 'Kevin', 'Andrew', 'Barbara', 'David', 'Nancy', 'Linda', 'Mark']
    
    # Try all permutations of the first 5 friends (to keep computation reasonable)
    for perm in permutations(friend_order[:5]):
        test_order = list(perm) + friend_order[5:]
        count, itinerary = evaluate_schedule(test_order)
        if count > best_count or (count == best_count and len(itinerary) > len(best_itinerary)):
            best_count = count
            best_itinerary = itinerary
    
    return best_itinerary

def main():
    itinerary = find_optimal_schedule()
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()