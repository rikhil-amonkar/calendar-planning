import constraint
from datetime import datetime, timedelta
import json

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    dt = datetime.strptime(time_str, "%H:%M")
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('North Beach', 'Pacific Heights'): 8,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Mission District'): 18,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Nob Hill'): 7,
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Mission District'): 18,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Nob Hill'): 8,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Mission District'): 14,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Nob Hill'): 9,
        ('Mission District', 'North Beach'): 17,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Chinatown'): 16,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Nob Hill'): 12,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'Mission District'): 13,
        ('Nob Hill', 'Golden Gate Park'): 17,
    }
    
    # Friend constraints
    friends = [
        {
            'name': 'James',
            'location': 'Pacific Heights',
            'available_start': '20:00',
            'available_end': '22:00',
            'min_duration': 120
        },
        {
            'name': 'Robert',
            'location': 'Chinatown',
            'available_start': '12:15',
            'available_end': '16:45',
            'min_duration': 90
        },
        {
            'name': 'Jeffrey',
            'location': 'Union Square',
            'available_start': '9:30',
            'available_end': '15:30',
            'min_duration': 120
        },
        {
            'name': 'Carol',
            'location': 'Mission District',
            'available_start': '18:15',
            'available_end': '21:15',
            'min_duration': 15
        },
        {
            'name': 'Mark',
            'location': 'Golden Gate Park',
            'available_start': '11:30',
            'available_end': '17:45',
            'min_duration': 15
        },
        {
            'name': 'Sandra',
            'location': 'Nob Hill',
            'available_start': '8:00',
            'available_end': '15:30',
            'min_duration': 15
        }
    ]
    
    # Convert times to minutes
    start_time_min = time_to_minutes('9:00')
    current_location = 'North Beach'
    
    problem = constraint.Problem()
    
    # Create variables for each friend: start time and duration
    for i, friend in enumerate(friends):
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        min_duration = friend['min_duration']
        
        # Start time must be within availability window
        problem.addVariable(f'start_{i}', range(available_start, available_end - min_duration + 1))
        # Duration must be at least minimum required
        problem.addVariable(f'duration_{i}', range(min_duration, available_end - available_start + 1))
    
    # Add constraints for travel time and ordering
    def travel_and_ordering_constraint(*args):
        # Extract all start times and durations
        starts = [args[i] for i in range(0, len(args), 2)]
        durations = [args[i+1] for i in range(0, len(args), 2)]
        ends = [starts[i] + durations[i] for i in range(len(starts))]
        
        # Create a list of meetings with start, end, location, and index
        meetings = []
        for i in range(len(friends)):
            meetings.append({
                'start': starts[i],
                'end': ends[i],
                'location': friends[i]['location'],
                'index': i
            })
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x['start'])
        
        # Check if we can travel between consecutive meetings
        current_time = start_time_min
        current_loc = current_location
        
        for meeting in meetings:
            # Travel to meeting location
            travel_time = travel_times.get((current_loc, meeting['location']), 999)
            if current_time + travel_time > meeting['start']:
                return False
            
            # Update current time and location
            current_time = meeting['end']
            current_loc = meeting['location']
        
        return True
    
    # Add the constraint
    all_vars = []
    for i in range(len(friends)):
        all_vars.append(f'start_{i}')
        all_vars.append(f'duration_{i}')
    
    problem.addConstraint(travel_and_ordering_constraint, all_vars)
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet as many friends as possible with minimum durations
        itinerary = []
        current_time = start_time_min
        current_loc = current_location
        
        # Sort friends by availability start time for greedy approach
        sorted_friends = sorted(friends, key=lambda x: time_to_minutes(x['available_start']))
        
        for friend in sorted_friends:
            available_start = time_to_minutes(friend['available_start'])
            available_end = time_to_minutes(friend['available_end'])
            min_duration = friend['min_duration']
            travel_time = travel_times.get((current_loc, friend['location']), 999)
            
            # Calculate earliest possible start time
            earliest_start = max(current_time + travel_time, available_start)
            
            if earliest_start + min_duration <= available_end:
                # We can meet this friend
                start_time = earliest_start
                end_time = start_time + min_duration
                
                itinerary.append({
                    "action": "meet",
                    "location": friend['location'],
                    "person": friend['name'],
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
                
                current_time = end_time
                current_loc = friend['location']
        
        result = {"itinerary": itinerary}
    else:
        # Use the first valid solution
        solution = solutions[0]
        itinerary = []
        
        # Create list of meetings from solution
        meetings = []
        for i in range(len(friends)):
            start = solution[f'start_{i}']
            duration = solution[f'duration_{i}']
            meetings.append({
                'start': start,
                'end': start + duration,
                'location': friends[i]['location'],
                'name': friends[i]['name']
            })
        
        # Sort by start time
        meetings.sort(key=lambda x: x['start'])
        
        for meeting in meetings:
            itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['name'],
                "start_time": minutes_to_time(meeting['start']),
                "end_time": minutes_to_time(meeting['end'])
            })
        
        result = {"itinerary": itinerary}
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()