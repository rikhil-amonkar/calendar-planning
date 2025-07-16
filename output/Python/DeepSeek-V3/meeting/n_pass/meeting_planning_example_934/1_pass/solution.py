import json
from itertools import permutations

# Travel times dictionary: from_location -> to_location -> minutes
travel_times = {
    'Nob Hill': {
        'Embarcadero': 9,
        'The Castro': 17,
        'Haight-Ashbury': 13,
        'Union Square': 7,
        'North Beach': 8,
        'Pacific Heights': 8,
        'Chinatown': 6,
        'Golden Gate Park': 17,
        'Marina District': 11,
        'Russian Hill': 5
    },
    'Embarcadero': {
        'Nob Hill': 10,
        'The Castro': 25,
        'Haight-Ashbury': 21,
        'Union Square': 10,
        'North Beach': 5,
        'Pacific Heights': 11,
        'Chinatown': 7,
        'Golden Gate Park': 25,
        'Marina District': 12,
        'Russian Hill': 8
    },
    'The Castro': {
        'Nob Hill': 16,
        'Embarcadero': 22,
        'Haight-Ashbury': 6,
        'Union Square': 19,
        'North Beach': 20,
        'Pacific Heights': 16,
        'Chinatown': 22,
        'Golden Gate Park': 11,
        'Marina District': 21,
        'Russian Hill': 18
    },
    'Haight-Ashbury': {
        'Nob Hill': 15,
        'Embarcadero': 20,
        'The Castro': 6,
        'Union Square': 19,
        'North Beach': 19,
        'Pacific Heights': 12,
        'Chinatown': 19,
        'Golden Gate Park': 7,
        'Marina District': 17,
        'Russian Hill': 17
    },
    'Union Square': {
        'Nob Hill': 9,
        'Embarcadero': 11,
        'The Castro': 17,
        'Haight-Ashbury': 18,
        'North Beach': 10,
        'Pacific Heights': 15,
        'Chinatown': 7,
        'Golden Gate Park': 22,
        'Marina District': 18,
        'Russian Hill': 13
    },
    'North Beach': {
        'Nob Hill': 7,
        'Embarcadero': 6,
        'The Castro': 23,
        'Haight-Ashbury': 18,
        'Union Square': 7,
        'Pacific Heights': 8,
        'Chinatown': 6,
        'Golden Gate Park': 22,
        'Marina District': 9,
        'Russian Hill': 4
    },
    'Pacific Heights': {
        'Nob Hill': 8,
        'Embarcadero': 10,
        'The Castro': 16,
        'Haight-Ashbury': 11,
        'Union Square': 12,
        'North Beach': 9,
        'Chinatown': 11,
        'Golden Gate Park': 15,
        'Marina District': 6,
        'Russian Hill': 7
    },
    'Chinatown': {
        'Nob Hill': 9,
        'Embarcadero': 5,
        'The Castro': 22,
        'Haight-Ashbury': 19,
        'Union Square': 7,
        'North Beach': 3,
        'Pacific Heights': 10,
        'Golden Gate Park': 23,
        'Marina District': 12,
        'Russian Hill': 7
    },
    'Golden Gate Park': {
        'Nob Hill': 20,
        'Embarcadero': 25,
        'The Castro': 13,
        'Haight-Ashbury': 7,
        'Union Square': 22,
        'North Beach': 23,
        'Pacific Heights': 16,
        'Chinatown': 23,
        'Marina District': 16,
        'Russian Hill': 19
    },
    'Marina District': {
        'Nob Hill': 12,
        'Embarcadero': 14,
        'The Castro': 22,
        'Haight-Ashbury': 16,
        'Union Square': 16,
        'North Beach': 11,
        'Pacific Heights': 7,
        'Chinatown': 15,
        'Golden Gate Park': 18,
        'Russian Hill': 8
    },
    'Russian Hill': {
        'Nob Hill': 5,
        'Embarcadero': 8,
        'The Castro': 21,
        'Haight-Ashbury': 17,
        'Union Square': 10,
        'North Beach': 5,
        'Pacific Heights': 7,
        'Chinatown': 9,
        'Golden Gate Park': 21,
        'Marina District': 7
    }
}

# People's availability and constraints
people = [
    {'name': 'Mary', 'location': 'Embarcadero', 'start': '20:00', 'end': '21:15', 'min_duration': 75},
    {'name': 'Kenneth', 'location': 'The Castro', 'start': '11:15', 'end': '19:15', 'min_duration': 30},
    {'name': 'Joseph', 'location': 'Haight-Ashbury', 'start': '20:00', 'end': '22:00', 'min_duration': 120},
    {'name': 'Sarah', 'location': 'Union Square', 'start': '11:45', 'end': '14:30', 'min_duration': 90},
    {'name': 'Thomas', 'location': 'North Beach', 'start': '19:15', 'end': '19:45', 'min_duration': 15},
    {'name': 'Daniel', 'location': 'Pacific Heights', 'start': '13:45', 'end': '20:30', 'min_duration': 15},
    {'name': 'Richard', 'location': 'Chinatown', 'start': '8:00', 'end': '18:45', 'min_duration': 30},
    {'name': 'Mark', 'location': 'Golden Gate Park', 'start': '17:30', 'end': '21:30', 'min_duration': 120},
    {'name': 'David', 'location': 'Marina District', 'start': '20:00', 'end': '21:00', 'min_duration': 60},
    {'name': 'Karen', 'location': 'Russian Hill', 'start': '13:15', 'end': '18:30', 'min_duration': 120}
]

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def get_travel_time(from_loc, to_loc):
    return travel_times.get(from_loc, {}).get(to_loc, float('inf'))

def is_schedule_valid(schedule):
    current_time = time_to_minutes('9:00')
    current_location = 'Nob Hill'
    
    for meeting in schedule:
        # Travel to meeting location
        travel_time = get_travel_time(current_location, meeting['location'])
        if travel_time == float('inf'):
            return False
        
        arrival_time = current_time + travel_time
        meeting_start = time_to_minutes(meeting['start'])
        meeting_end = time_to_minutes(meeting['end'])
        
        # Check if we arrive before meeting ends and can stay for min duration
        if arrival_time > meeting_end:
            return False
        actual_start = max(arrival_time, meeting_start)
        actual_end = min(actual_start + meeting['min_duration'], meeting_end)
        
        if actual_end - actual_start < meeting['min_duration']:
            return False
        
        current_time = actual_end
        current_location = meeting['location']
    
    return True

def calculate_total_meeting_time(schedule):
    total = 0
    for meeting in schedule:
        total += meeting['min_duration']
    return total

def generate_possible_schedules():
    # Filter people who can't be met due to time constraints
    feasible_people = []
    for person in people:
        if person['min_duration'] <= (time_to_minutes(person['end']) - time_to_minutes(person['start'])):
            feasible_people.append(person)
    
    best_schedule = []
    max_duration = 0
    
    # Try all permutations of up to 5 people (to keep computation feasible)
    from itertools import combinations
    for r in range(1, min(6, len(feasible_people) + 1)):
        for group in combinations(feasible_people, r):
            for perm in permutations(group):
                schedule = []
                for person in perm:
                    schedule.append({
                        'location': person['location'],
                        'name': person['name'],
                        'start': person['start'],
                        'end': person['end'],
                        'min_duration': person['min_duration']
                    })
                if is_schedule_valid(schedule):
                    total_duration = calculate_total_meeting_time(schedule)
                    if total_duration > max_duration:
                        max_duration = total_duration
                        best_schedule = schedule
    
    return best_schedule

def build_itinerary(schedule):
    itinerary = []
    current_time = time_to_minutes('9:00')
    current_location = 'Nob Hill'
    
    for meeting in schedule:
        # Travel
        travel_time = get_travel_time(current_location, meeting['location'])
        travel_start = minutes_to_time(current_time)
        current_time += travel_time
        travel_end = minutes_to_time(current_time)
        
        itinerary.append({
            'action': 'travel',
            'from': current_location,
            'to': meeting['location'],
            'start_time': travel_start,
            'end_time': travel_end
        })
        
        # Meeting
        meeting_start = time_to_minutes(meeting['start'])
        meeting_end = time_to_minutes(meeting['end'])
        
        actual_start = max(current_time, meeting_start)
        actual_end = min(actual_start + meeting['min_duration'], meeting_end)
        
        itinerary.append({
            'action': 'meet',
            'location': meeting['location'],
            'person': meeting['name'],
            'start_time': minutes_to_time(actual_start),
            'end_time': minutes_to_time(actual_end)
        })
        
        current_time = actual_end
        current_location = meeting['location']
    
    return itinerary

def main():
    best_schedule = generate_possible_schedules()
    itinerary = build_itinerary(best_schedule)
    
    # Filter out only meet actions for final output
    meet_actions = [item for item in itinerary if item['action'] == 'meet']
    
    result = {
        "itinerary": meet_actions
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()