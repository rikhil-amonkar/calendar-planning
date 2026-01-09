from constraint import Problem, AllDifferentConstraint
import json

def main():
    # Define travel times as a dictionary
    travel_times = {
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Embarcadero'): 22,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('The Castro', 'Richmond District'): 16,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Marina District'): 21,
        ('The Castro', 'Presidio'): 20,
        ('The Castro', 'Union Square'): 19,
        ('The Castro', 'Financial District'): 21,
        ('North Beach', 'The Castro'): 23,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('North Beach', 'Richmond District'): 18,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Marina District'): 9,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Financial District'): 8,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'North Beach'): 23,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Embarcadero', 'The Castro'): 25,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Haight-Ashbury'): 21,
        ('Embarcadero', 'Richmond District'): 21,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Marina District'): 12,
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Union Square'): 10,
        ('Embarcadero', 'Financial District'): 5,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Embarcadero'): 20,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Union Square'): 19,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Richmond District', 'The Castro'): 16,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Richmond District', 'Embarcadero'): 19,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Marina District'): 9,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Union Square'): 21,
        ('Richmond District', 'Financial District'): 22,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('Nob Hill', 'Richmond District'): 14,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'Presidio'): 17,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'Financial District'): 9,
        ('Marina District', 'The Castro'): 22,
        ('Marina District', 'North Beach'): 11,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Marina District', 'Embarcadero'): 14,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Richmond District'): 11,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Presidio'): 10,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'Financial District'): 17,
        ('Presidio', 'The Castro'): 21,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Nob Hill'): 18,
        ('Presidio', 'Marina District'): 11,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'Financial District'): 23,
        ('Union Square', 'The Castro'): 17,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Embarcadero'): 11,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Richmond District'): 20,
        ('Union Square', 'Nob Hill'): 9,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Financial District'): 9,
        ('Financial District', 'The Castro'): 20,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Haight-Ashbury'): 19,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'Nob Hill'): 8,
        ('Financial District', 'Marina District'): 15,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Union Square'): 9
    }

    # Define friends' availability and minimum meeting times
    friends = {
        'Steven': {
            'location': 'North Beach',
            'start': 17.5,  # 5:30 PM
            'end': 20.5,    # 8:30 PM
            'min_duration': 0.25  # 15 minutes
        },
        'Sarah': {
            'location': 'Golden Gate Park',
            'start': 17.0,  # 5:00 PM
            'end': 19.25,   # 7:15 PM
            'min_duration': 1.25  # 75 minutes
        },
        'Brian': {
            'location': 'Embarcadero',
            'start': 14.25, # 2:15 PM
            'end': 16.0,    # 4:00 PM
            'min_duration': 1.75  # 105 minutes
        },
        'Stephanie': {
            'location': 'Haight-Ashbury',
            'start': 10.25, # 10:15 AM
            'end': 12.25,   # 12:15 PM
            'min_duration': 1.25  # 75 minutes
        },
        'Melissa': {
            'location': 'Richmond District',
            'start': 14.0,  # 2:00 PM
            'end': 19.5,    # 7:30 PM
            'min_duration': 0.5  # 30 minutes
        },
        'Nancy': {
            'location': 'Nob Hill',
            'start': 8.25,  # 8:15 AM
            'end': 12.75,   # 12:45 PM
            'min_duration': 1.5  # 90 minutes
        },
        'David': {
            'location': 'Marina District',
            'start': 11.25, # 11:15 AM
            'end': 13.25,   # 1:15 PM
            'min_duration': 2.0  # 120 minutes
        },
        'James': {
            'location': 'Presidio',
            'start': 15.0,  # 3:00 PM
            'end': 18.25,   # 6:15 PM
            'min_duration': 2.0  # 120 minutes
        },
        'Elizabeth': {
            'location': 'Union Square',
            'start': 11.5,  # 11:30 AM
            'end': 21.0,    # 9:00 PM
            'min_duration': 1.0  # 60 minutes
        },
        'Robert': {
            'location': 'Financial District',
            'start': 13.25, # 1:15 PM
            'end': 15.25,   # 3:15 PM
            'min_duration': 0.75  # 45 minutes
        }
    }

    # Create constraint problem
    problem = Problem()

    # Define variables for each friend: whether to meet them and meeting time
    for friend in friends:
        problem.addVariable(f"{friend}_meet", [0, 1])
        problem.addVariable(f"{friend}_start", range(0, 2400, 5))  # Time in minutes from 0:00
        problem.addVariable(f"{friend}_duration", range(0, 241, 5))  # Duration in minutes

    # Add constraints
    current_location = 'The Castro'
    current_time = 9.0 * 60  # 9:00 AM in minutes
    
    # Helper function to convert time to minutes
    def to_minutes(time_float):
        hours = int(time_float)
        minutes = int((time_float - hours) * 60)
        return hours * 60 + minutes
    
    # Helper function to convert minutes to time string
    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    # Simple greedy scheduling (constraint library not well-suited for this complex scheduling)
    # We'll implement a heuristic approach
    
    itinerary = []
    
    # Sort friends by their availability start time
    sorted_friends = sorted(friends.items(), key=lambda x: x[1]['start'])
    
    current_location = 'The Castro'
    current_time_minutes = to_minutes(9.0)  # Start at 9:00 AM
    
    for friend, info in sorted_friends:
        location = info['location']
        start_available = to_minutes(info['start'])
        end_available = to_minutes(info['end'])
        min_duration_minutes = int(info['min_duration'] * 60)
        
        # Calculate travel time
        travel_time = travel_times.get((current_location, location), 30)
        
        # Earliest we can arrive
        earliest_arrival = current_time_minutes + travel_time
        
        # If we can make it during their availability
        if earliest_arrival <= end_available:
            # Start meeting as soon as possible after arrival and their availability starts
            meeting_start = max(earliest_arrival, start_available)
            
            # Calculate how long we can meet (until they leave or we need to leave for next meeting)
            max_possible_duration = end_available - meeting_start
            
            # If we can meet for at least the minimum duration
            if max_possible_duration >= min_duration_minutes:
                # Meet for the minimum duration
                meeting_end = meeting_start + min_duration_minutes
                
                # Add to itinerary
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": friend,
                    "start_time": to_time_str(meeting_start),
                    "end_time": to_time_str(meeting_end)
                })
                
                # Update current location and time
                current_location = location
                current_time_minutes = meeting_end
    
    # Create output
    output = {
        "itinerary": itinerary
    }
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()