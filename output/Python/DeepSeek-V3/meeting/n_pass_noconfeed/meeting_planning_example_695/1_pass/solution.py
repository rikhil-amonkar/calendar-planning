import json
from itertools import permutations

# Travel times dictionary: from_location -> to_location -> minutes
travel_times = {
    'Bayview': {
        'Nob Hill': 20,
        'Union Square': 17,
        'Chinatown': 18,
        'The Castro': 20,
        'Presidio': 31,
        'Pacific Heights': 23,
        'Russian Hill': 23
    },
    'Nob Hill': {
        'Bayview': 19,
        'Union Square': 7,
        'Chinatown': 6,
        'The Castro': 17,
        'Presidio': 17,
        'Pacific Heights': 8,
        'Russian Hill': 5
    },
    'Union Square': {
        'Bayview': 15,
        'Nob Hill': 9,
        'Chinatown': 7,
        'The Castro': 19,
        'Presidio': 24,
        'Pacific Heights': 15,
        'Russian Hill': 13
    },
    'Chinatown': {
        'Bayview': 22,
        'Nob Hill': 8,
        'Union Square': 7,
        'The Castro': 22,
        'Presidio': 19,
        'Pacific Heights': 10,
        'Russian Hill': 7
    },
    'The Castro': {
        'Bayview': 19,
        'Nob Hill': 16,
        'Union Square': 19,
        'Chinatown': 20,
        'Presidio': 20,
        'Pacific Heights': 16,
        'Russian Hill': 18
    },
    'Presidio': {
        'Bayview': 31,
        'Nob Hill': 18,
        'Union Square': 22,
        'Chinatown': 21,
        'The Castro': 21,
        'Pacific Heights': 11,
        'Russian Hill': 14
    },
    'Pacific Heights': {
        'Bayview': 22,
        'Nob Hill': 8,
        'Union Square': 12,
        'Chinatown': 11,
        'The Castro': 16,
        'Presidio': 11,
        'Russian Hill': 7
    },
    'Russian Hill': {
        'Bayview': 23,
        'Nob Hill': 5,
        'Union Square': 11,
        'Chinatown': 9,
        'The Castro': 21,
        'Presidio': 14,
        'Pacific Heights': 7
    }
}

# People's availability
people = {
    'Paul': {'location': 'Nob Hill', 'start': 16.25, 'end': 21.25, 'duration': 1.0},
    'Carol': {'location': 'Union Square', 'start': 18.0, 'end': 20.25, 'duration': 2.0},
    'Patricia': {'location': 'Chinatown', 'start': 20.0, 'end': 21.5, 'duration': 1.25},
    'Karen': {'location': 'The Castro', 'start': 17.0, 'end': 19.0, 'duration': 0.75},
    'Nancy': {'location': 'Presidio', 'start': 11.75, 'end': 22.0, 'duration': 0.5},
    'Jeffrey': {'location': 'Pacific Heights', 'start': 20.0, 'end': 20.75, 'duration': 0.75},
    'Matthew': {'location': 'Russian Hill', 'start': 15.75, 'end': 21.75, 'duration': 1.25}
}

def time_to_float(time_str):
    hours, minutes = map(float, time_str.split(':'))
    return hours + minutes / 60

def float_to_time(time_float):
    hours = int(time_float)
    minutes = int((time_float - hours) * 60)
    return f"{hours}:{minutes:02d}"

def calculate_schedule(order):
    current_time = 9.0  # Start at Bayview at 9:00 AM
    current_location = 'Bayview'
    schedule = []
    met_people = set()
    
    for person in order:
        if person in met_people:
            continue
            
        info = people[person]
        location = info['location']
        travel_time = travel_times[current_location][location] / 60
        arrival_time = current_time + travel_time
        
        # Check if we can meet this person
        meeting_start = max(arrival_time, info['start'])
        meeting_end = meeting_start + info['duration']
        
        if meeting_end > info['end']:
            continue  # Can't meet this person in this order
            
        # Add to schedule
        schedule.append({
            'action': 'meet',
            'location': location,
            'person': person,
            'start_time': float_to_time(meeting_start),
            'end_time': float_to_time(meeting_end)
        })
        
        met_people.add(person)
        current_time = meeting_end
        current_location = location
    
    return schedule

def evaluate_schedule(schedule):
    return len(schedule)

def main():
    best_schedule = []
    best_score = 0
    
    # Try all possible orders (limited to 5 people for performance)
    for order in permutations(people.keys(), 5):
        schedule = calculate_schedule(order)
        score = evaluate_schedule(schedule)
        
        if score > best_score:
            best_score = score
            best_schedule = schedule
    
    # If we didn't find a schedule meeting 5, try 4
    if best_score < 5:
        for order in permutations(people.keys(), 4):
            schedule = calculate_schedule(order)
            score = evaluate_schedule(schedule)
            
            if score > best_score:
                best_score = score
                best_schedule = schedule
    
    # Output the best schedule found
    result = {
        "itinerary": best_schedule
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()