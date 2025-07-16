import json
from itertools import permutations

# Travel times between locations in minutes
travel_times = {
    'Nob Hill': {
        'Embarcadero': 15,
        'The Castro': 20,
        'Haight-Ashbury': 15,
        'Union Square': 10,
        'North Beach': 10,
        'Pacific Heights': 10,
        'Chinatown': 5,
        'Golden Gate Park': 25,
        'Marina District': 15,
        'Russian Hill': 5
    },
    'Embarcadero': {
        'Nob Hill': 15,
        'The Castro': 25,
        'Haight-Ashbury': 30,
        'Union Square': 15,
        'North Beach': 20,
        'Pacific Heights': 20,
        'Chinatown': 10,
        'Golden Gate Park': 35,
        'Marina District': 25,
        'Russian Hill': 20
    },
    'The Castro': {
        'Nob Hill': 20,
        'Embarcadero': 25,
        'Haight-Ashbury': 10,
        'Union Square': 15,
        'North Beach': 25,
        'Pacific Heights': 20,
        'Chinatown': 15,
        'Golden Gate Park': 15,
        'Marina District': 30,
        'Russian Hill': 25
    },
    'Union Square': {
        'Nob Hill': 10,
        'Embarcadero': 15,
        'The Castro': 15,
        'Haight-Ashbury': 15,
        'North Beach': 15,
        'Pacific Heights': 10,
        'Chinatown': 5,
        'Golden Gate Park': 25,
        'Marina District': 20,
        'Russian Hill': 10
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
    return f"{h:02d}:{m:02d}"

def get_travel_time(from_loc, to_loc):
    if from_loc == to_loc:
        return 0
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
        
        # Check if we can make it to the meeting and stay for min duration
        if arrival_time > meeting_end - meeting['min_duration']:
            return False
        
        actual_start = max(arrival_time, meeting_start)
        if actual_start + meeting['min_duration'] > meeting_end:
            return False
        
        current_time = actual_start + meeting['min_duration']
        current_location = meeting['location']
    
    return True

def calculate_total_meeting_time(schedule):
    total = 0
    for meeting in schedule:
        total += meeting['min_duration']
    return total

def generate_possible_schedules():
    feasible_people = [p for p in people if time_to_minutes(p['end']) - time_to_minutes(p['start']) >= p['min_duration']]
    
    best_schedule = []
    max_duration = 0
    
    # Try all permutations of up to 5 people
    from itertools import combinations
    for r in range(min(5, len(feasible_people)), 0, -1):
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
                        # Return first found maximum (greedy approach)
                        return best_schedule
    
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
        actual_end = actual_start + meeting['min_duration']
        
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
    if not best_schedule:
        print(json.dumps({"itinerary": []}, indent=2))
        return
    
    # Adjust schedule to ensure enough travel time between meetings
    adjusted_schedule = []
    current_time = time_to_minutes('9:00')
    current_location = 'Nob Hill'
    
    for meeting in best_schedule:
        travel_time = get_travel_time(current_location, meeting['location'])
        arrival_time = current_time + travel_time
        meeting_start = time_to_minutes(meeting['start'])
        meeting_end = time_to_minutes(meeting['end'])
        
        actual_start = max(arrival_time, meeting_start)
        actual_end = actual_start + meeting['min_duration']
        
        # Ensure we have enough time for the meeting
        if actual_end > meeting_end:
            continue  # Skip this meeting if we can't make it
        
        adjusted_schedule.append({
            'location': meeting['location'],
            'name': meeting['name'],
            'start': minutes_to_time(actual_start),
            'end': minutes_to_time(actual_end),
            'min_duration': meeting['min_duration']
        })
        
        current_time = actual_end
        current_location = meeting['location']
    
    itinerary = build_itinerary(adjusted_schedule)
    
    # Filter out only meet actions for final output
    meet_actions = [item for item in itinerary if item['action'] == 'meet']
    
    result = {
        "itinerary": meet_actions
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()