import json
from itertools import permutations

# Travel times dictionary: travel_times[from_location][to_location] = minutes
travel_times = {
    'Embarcadero': {
        'Richmond District': 21,
        'Union Square': 10,
        'Financial District': 5,
        'Pacific Heights': 11,
        'Nob Hill': 10,
        'Bayview': 21
    },
    'Richmond District': {
        'Embarcadero': 19,
        'Union Square': 21,
        'Financial District': 22,
        'Pacific Heights': 10,
        'Nob Hill': 17,
        'Bayview': 26
    },
    'Union Square': {
        'Embarcadero': 11,
        'Richmond District': 20,
        'Financial District': 9,
        'Pacific Heights': 15,
        'Nob Hill': 9,
        'Bayview': 15
    },
    'Financial District': {
        'Embarcadero': 4,
        'Richmond District': 21,
        'Union Square': 9,
        'Pacific Heights': 13,
        'Nob Hill': 8,
        'Bayview': 19
    },
    'Pacific Heights': {
        'Embarcadero': 10,
        'Richmond District': 12,
        'Union Square': 12,
        'Financial District': 13,
        'Nob Hill': 8,
        'Bayview': 22
    },
    'Nob Hill': {
        'Embarcadero': 9,
        'Richmond District': 14,
        'Union Square': 7,
        'Financial District': 9,
        'Pacific Heights': 8,
        'Bayview': 19
    },
    'Bayview': {
        'Embarcadero': 19,
        'Richmond District': 25,
        'Union Square': 17,
        'Financial District': 19,
        'Pacific Heights': 23,
        'Nob Hill': 20
    }
}

# Friend data: name, location, available_start, available_end, min_duration
friends = [
    ('Kenneth', 'Richmond District', 21.25, 22.0, 0.5),
    ('Lisa', 'Union Square', 9.0, 16.5, 0.75),
    ('Joshua', 'Financial District', 12.0, 15.25, 0.25),
    ('Nancy', 'Pacific Heights', 8.0, 11.5, 1.5),
    ('Andrew', 'Nob Hill', 11.5, 20.25, 1.0),
    ('John', 'Bayview', 16.75, 21.5, 1.25)
]

def time_to_float(time_str):
    if isinstance(time_str, float):
        return time_str
    hours, minutes = map(float, time_str.split(':'))
    return hours + minutes / 60.0

def float_to_time(time_float):
    hours = int(time_float)
    minutes = int((time_float - hours) * 60)
    return f"{hours}:{minutes:02d}"

def calculate_schedule(order):
    current_time = 9.0  # Start at Embarcadero at 9:00
    current_location = 'Embarcadero'
    schedule = []
    met_friends = set()
    
    for friend_idx in order:
        name, location, avail_start, avail_end, min_duration = friends[friend_idx]
        
        # Calculate travel time
        travel_time = travel_times[current_location].get(location, 0) / 60.0
        arrival_time = current_time + travel_time
        
        # Check if we can meet this friend
        meeting_start = max(arrival_time, avail_start)
        meeting_end = meeting_start + min_duration
        
        if meeting_end <= avail_end:
            # Add travel and meeting to schedule
            if travel_time > 0:
                schedule.append({
                    "action": "travel",
                    "from": current_location,
                    "to": location,
                    "start_time": float_to_time(current_time),
                    "end_time": float_to_time(arrival_time)
                })
            
            schedule.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": float_to_time(meeting_start),
                "end_time": float_to_time(meeting_end)
            })
            
            met_friends.add(friend_idx)
            current_time = meeting_end
            current_location = location
        else:
            # Can't meet this friend, skip
            continue
    
    return schedule, len(met_friends)

def find_optimal_schedule():
    best_schedule = []
    max_meetings = 0
    
    # Try all possible meeting orders (permutations of friends)
    for order in permutations(range(len(friends))):
        schedule, num_meetings = calculate_schedule(order)
        if num_meetings > max_meetings:
            max_meetings = num_meetings
            best_schedule = schedule
        elif num_meetings == max_meetings and len(schedule) > 0:
            # Prefer schedules that end earlier
            last_meeting_end = time_to_float(schedule[-1]['end_time'])
            current_last_end = time_to_float(best_schedule[-1]['end_time']) if best_schedule else 24.0
            if last_meeting_end < current_last_end:
                best_schedule = schedule
    
    # Filter out travel segments for the final itinerary
    itinerary = [item for item in best_schedule if item['action'] == 'meet']
    return itinerary

def main():
    itinerary = find_optimal_schedule()
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()