import json
from itertools import permutations

# Travel times in minutes between locations
travel_times = {
    'Presidio': {
        'Richmond District': 7,
        'North Beach': 18,
        'Financial District': 23,
        'Golden Gate Park': 12,
        'Union Square': 22
    },
    'Richmond District': {
        'Presidio': 7,
        'North Beach': 17,
        'Financial District': 22,
        'Golden Gate Park': 9,
        'Union Square': 21
    },
    'North Beach': {
        'Presidio': 17,
        'Richmond District': 18,
        'Financial District': 8,
        'Golden Gate Park': 22,
        'Union Square': 7
    },
    'Financial District': {
        'Presidio': 22,
        'Richmond District': 21,
        'North Beach': 7,
        'Golden Gate Park': 23,
        'Union Square': 9
    },
    'Golden Gate Park': {
        'Presidio': 11,
        'Richmond District': 7,
        'North Beach': 24,
        'Financial District': 26,
        'Union Square': 22
    },
    'Union Square': {
        'Presidio': 24,
        'Richmond District': 20,
        'North Beach': 10,
        'Financial District': 9,
        'Golden Gate Park': 22
    }
}

# Friend constraints
friends = {
    'Jason': {
        'location': 'Richmond District',
        'start': 13 * 60,  # 1:00 PM in minutes
        'end': 20 * 60 + 45,  # 8:45 PM in minutes
        'duration': 90  # minutes
    },
    'Melissa': {
        'location': 'North Beach',
        'start': 18 * 60 + 45,  # 6:45 PM in minutes
        'end': 20 * 60 + 15,  # 8:15 PM in minutes
        'duration': 45  # minutes
    },
    'Brian': {
        'location': 'Financial District',
        'start': 9 * 60 + 45,  # 9:45 AM in minutes
        'end': 21 * 60 + 45,  # 9:45 PM in minutes
        'duration': 15  # minutes
    },
    'Elizabeth': {
        'location': 'Golden Gate Park',
        'start': 8 * 60 + 45,  # 8:45 AM in minutes
        'end': 21 * 60 + 30,  # 9:30 PM in minutes
        'duration': 105  # minutes
    },
    'Laura': {
        'location': 'Union Square',
        'start': 14 * 60 + 15,  # 2:15 PM in minutes
        'end': 19 * 60 + 30,  # 7:30 PM in minutes
        'duration': 75  # minutes
    }
}

def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def str_to_time(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def calculate_schedule(order):
    current_location = 'Presidio'
    current_time = 9 * 60  # 9:00 AM
    schedule = []
    met_friends = set()
    
    for friend in order:
        if friend in met_friends:
            continue
        friend_info = friends[friend]
        location = friend_info['location']
        travel_time = travel_times[current_location].get(location, float('inf'))
        
        arrival_time = current_time + travel_time
        start_time = max(arrival_time, friend_info['start'])
        end_time = start_time + friend_info['duration']
        
        if end_time > friend_info['end']:
            continue  # Can't meet this friend with current schedule
        
        schedule.append({
            'action': 'meet',
            'location': location,
            'person': friend,
            'start_time': time_to_str(start_time),
            'end_time': time_to_str(end_time)
        })
        met_friends.add(friend)
        current_time = end_time
        current_location = location
    
    return schedule, len(met_friends)

def find_optimal_schedule():
    best_schedule = []
    max_met = 0
    
    # Try all permutations of friends to find the best order
    for perm in permutations(friends.keys()):
        schedule, met = calculate_schedule(perm)
        if met > max_met or (met == max_met and len(schedule) > len(best_schedule)):
            best_schedule = schedule
            max_met = met
    
    return best_schedule

def main():
    optimal_schedule = find_optimal_schedule()
    result = {
        "itinerary": optimal_schedule
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()