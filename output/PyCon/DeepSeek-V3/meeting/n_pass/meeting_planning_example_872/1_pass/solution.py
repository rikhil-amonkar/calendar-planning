from constraint import Problem, AllDifferentConstraint
import json

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes (symmetric)
    travel_times = {
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Nob Hill'): 18,
        ('Presidio', 'Russian Hill'): 14,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Financial District'): 23,
        ('Presidio', 'Marina District'): 11,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Union Square'): 19,
        ('Haight-Ashbury', 'Embarcadero'): 20,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Nob Hill', 'Financial District'): 9,
        ('Nob Hill', 'Marina District'): 11,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Union Square'): 10,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Russian Hill', 'Financial District'): 11,
        ('Russian Hill', 'Marina District'): 7,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'Marina District'): 9,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Embarcadero'): 5,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Marina District'): 12,
        ('Union Square', 'Embarcadero'): 11,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Marina District'): 18,
        ('Embarcadero', 'Financial District'): 5,
        ('Embarcadero', 'Marina District'): 12,
        ('Financial District', 'Marina District'): 15,
    }
    
    # Make symmetric
    symmetric_travel = travel_times.copy()
    for (loc1, loc2), time in travel_times.items():
        symmetric_travel[(loc2, loc1)] = time
    
    # Friend constraints
    friends = [
        {'name': 'Karen', 'location': 'Haight-Ashbury', 'available_start': '21:00', 'available_end': '21:45', 'duration': 45},
        {'name': 'Jessica', 'location': 'Nob Hill', 'available_start': '13:45', 'available_end': '21:00', 'duration': 90},
        {'name': 'Brian', 'location': 'Russian Hill', 'available_start': '15:30', 'available_end': '21:45', 'duration': 60},
        {'name': 'Kenneth', 'location': 'North Beach', 'available_start': '9:45', 'available_end': '21:00', 'duration': 30},
        {'name': 'Jason', 'location': 'Chinatown', 'available_start': '8:15', 'available_end': '11:45', 'duration': 75},
        {'name': 'Stephanie', 'location': 'Union Square', 'available_start': '14:45', 'available_end': '18:45', 'duration': 105},
        {'name': 'Kimberly', 'location': 'Embarcadero', 'available_start': '9:45', 'available_end': '19:30', 'duration': 75},
        {'name': 'Steven', 'location': 'Financial District', 'available_start': '7:15', 'available_end': '21:15', 'duration': 60},
        {'name': 'Mark', 'location': 'Marina District', 'available_start': '10:15', 'available_end': '13:00', 'duration': 75}
    ]
    
    # Convert times to minutes
    for friend in friends:
        friend['available_start_min'] = time_to_minutes(friend['available_start'])
        friend['available_end_min'] = time_to_minutes(friend['available_end'])
    
    # Start at Presidio at 9:00 AM
    start_time_min = time_to_minutes('9:00')
    
    problem = Problem()
    
    # Variables: start time for each meeting (in minutes since midnight)
    friend_names = [friend['name'] for friend in friends]
    for friend in friends:
        # Start time must be within friend's availability window, adjusted for duration
        min_start = friend['available_start_min']
        max_start = friend['available_end_min'] - friend['duration']
        problem.addVariable(friend['name'], range(min_start, max_start + 1))
    
    # Add travel time constraints
    for i, friend1 in enumerate(friends):
        for j, friend2 in enumerate(friends):
            if i != j:
                loc1 = friend1['location']
                loc2 = friend2['location']
                
                # Get travel time between locations
                if loc1 == loc2:
                    travel_time = 0
                else:
                    travel_time = symmetric_travel.get((loc1, loc2), symmetric_travel.get((loc2, loc1), 0))
                
                # Constraint: friend2 meeting must start after friend1 meeting ends + travel time
                def travel_constraint(start1, start2, f1=friend1, f2=friend2, tt=travel_time):
                    end1 = start1 + f1['duration']
                    return end1 + tt <= start2
                
                problem.addConstraint(travel_constraint, [friend1['name'], friend2['name']])
    
    # Start time constraint: first meeting must be after arriving at Presidio + travel to first location
    def start_constraint(*starts):
        # Find the earliest start time among all meetings
        earliest_start = min(starts)
        
        # Check if we can reach the earliest meeting location from Presidio in time
        earliest_friend = None
        for friend in friends:
            if starts[friend_names.index(friend['name'])] == earliest_start:
                earliest_friend = friend
                break
        
        if earliest_friend:
            travel_from_presidio = symmetric_travel.get(('Presidio', earliest_friend['location']), 0)
            return start_time_min + travel_from_presidio <= earliest_start
        return False
    
    problem.addConstraint(start_constraint, friend_names)
    
    # Try to maximize number of meetings by finding a solution
    solution = problem.getSolution()
    
    if solution:
        # Create itinerary
        itinerary = []
        
        # Sort meetings by start time
        sorted_meetings = sorted([(friend['name'], start_time) for friend, start_time in zip(friends, [solution[friend['name']] for friend in friends])], 
                                key=lambda x: x[1])
        
        for name, start_min in sorted_meetings:
            friend = next(f for f in friends if f['name'] == name)
            end_min = start_min + friend['duration']
            
            itinerary.append({
                "action": "meet",
                "location": friend['location'],
                "person": friend['name'],
                "start_time": minutes_to_time(start_min),
                "end_time": minutes_to_time(end_min)
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # Fallback: try to schedule as many as possible
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()