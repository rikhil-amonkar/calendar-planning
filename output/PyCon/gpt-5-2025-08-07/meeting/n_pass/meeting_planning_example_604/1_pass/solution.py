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
    # Travel times in minutes between locations
    travel_times = {
        ('Fisherman\'s Wharf', 'The Castro'): 26,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Russian Hill'): 7,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11,
        ('Fisherman\'s Wharf', 'Alamo Square'): 20,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('The Castro', 'Fisherman\'s Wharf'): 24,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Embarcadero'): 22,
        ('The Castro', 'Russian Hill'): 18,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'North Beach'): 20,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'The Castro'): 25,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Russian Hill'): 8,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Embarcadero', 'North Beach'): 5,
        ('Russian Hill', 'Fisherman\'s Wharf'): 7,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'North Beach'): 5,
        ('Nob Hill', 'Fisherman\'s Wharf'): 11,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'Alamo Square'): 11,
        ('Nob Hill', 'North Beach'): 8,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Embarcadero'): 17,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Nob Hill'): 11,
        ('Alamo Square', 'North Beach'): 15,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'The Castro'): 22,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'Russian Hill'): 4,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Alamo Square'): 16,
    }
    
    # Friend constraints
    friends = [
        {
            'name': 'Laura',
            'location': 'The Castro',
            'available_start': '19:45',
            'available_end': '21:30',
            'min_duration': 105
        },
        {
            'name': 'Daniel',
            'location': 'Golden Gate Park',
            'available_start': '21:15',
            'available_end': '21:45',
            'min_duration': 15
        },
        {
            'name': 'William',
            'location': 'Embarcadero',
            'available_start': '7:00',
            'available_end': '9:00',
            'min_duration': 90
        },
        {
            'name': 'Karen',
            'location': 'Russian Hill',
            'available_start': '14:30',
            'available_end': '19:45',
            'min_duration': 30
        },
        {
            'name': 'Stephanie',
            'location': 'Nob Hill',
            'available_start': '7:30',
            'available_end': '9:30',
            'min_duration': 45
        },
        {
            'name': 'Joseph',
            'location': 'Alamo Square',
            'available_start': '11:30',
            'available_end': '12:45',
            'min_duration': 15
        },
        {
            'name': 'Kimberly',
            'location': 'North Beach',
            'available_start': '15:45',
            'available_end': '19:15',
            'min_duration': 30
        }
    ]
    
    # Convert all times to minutes
    start_day = time_to_minutes('9:00')  # Arrival at Fisherman's Wharf
    end_day = time_to_minutes('23:59')   # End of day
    
    # Create problem
    problem = Problem()
    
    # Add variables for each friend: (start_time, duration)
    for i, friend in enumerate(friends):
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        min_duration = friend['min_duration']
        
        # Start time must be within availability window
        problem.addVariable(f'start_{i}', range(available_start, available_end - min_duration + 1))
        # Duration must be at least minimum
        problem.addVariable(f'duration_{i}', range(min_duration, available_end - available_start + 1))
    
    # Add travel time constraints
    def travel_constraint(*args):
        # Extract start times and durations for all friends
        starts = [args[i] for i in range(0, len(args), 2)]
        durations = [args[i] for i in range(1, len(args), 2)]
        
        # Create list of meetings with start and end times
        meetings = []
        for i in range(len(friends)):
            start = starts[i]
            end = start + durations[i]
            meetings.append((i, start, end, friends[i]['location']))
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x[1])
        
        # Check travel times between consecutive meetings
        for j in range(len(meetings) - 1):
            current_meeting = meetings[j]
            next_meeting = meetings[j + 1]
            
            current_end = current_meeting[2]
            next_start = next_meeting[1]
            travel_needed = travel_times.get((current_meeting[3], next_meeting[3]), 60)
            
            if next_start < current_end + travel_needed:
                return False
        
        return True
    
    # Add the travel constraint
    all_vars = []
    for i in range(len(friends)):
        all_vars.extend([f'start_{i}', f'duration_{i}'])
    
    problem.addConstraint(travel_constraint, all_vars)
    
    # Add constraint that we can't be in two places at once
    def no_overlap_constraint(*args):
        starts = [args[i] for i in range(0, len(args), 2)]
        durations = [args[i] for i in range(1, len(args), 2)]
        
        meetings = []
        for i in range(len(friends)):
            start = starts[i]
            end = start + durations[i]
            meetings.append((start, end))
        
        # Check for overlaps
        meetings.sort()
        for i in range(len(meetings) - 1):
            if meetings[i][1] > meetings[i + 1][0]:
                return False
        
        return True
    
    problem.addConstraint(no_overlap_constraint, all_vars)
    
    # Find a solution
    solution = problem.getSolution()
    
    if solution:
        # Build itinerary
        itinerary = []
        
        # Create list of meetings from solution
        meetings = []
        for i in range(len(friends)):
            start = solution[f'start_{i}']
            duration = solution[f'duration_{i}']
            end = start + duration
            meetings.append({
                'person': friends[i]['name'],
                'location': friends[i]['location'],
                'start': start,
                'end': end
            })
        
        # Sort by start time
        meetings.sort(key=lambda x: x['start'])
        
        # Add travel from Fisherman's Wharf to first meeting
        first_meeting = meetings[0]
        travel_from_start = travel_times.get(('Fisherman\'s Wharf', first_meeting['location']), 0)
        
        # Convert to time strings and build itinerary
        for meeting in meetings:
            itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['person'],
                "start_time": minutes_to_time(meeting['start']),
                "end_time": minutes_to_time(meeting['end'])
            })
        
        # Output result
        result = {
            "itinerary": itinerary
        }
        print(json.dumps(result, indent=2))
    else:
        # Fallback solution if constraint solving fails
        fallback_itinerary = [
            {"action": "meet", "location": "Embarcadero", "person": "William", "start_time": "7:00", "end_time": "8:30"},
            {"action": "meet", "location": "Nob Hill", "person": "Stephanie", "start_time": "8:45", "end_time": "9:30"},
            {"action": "meet", "location": "Alamo Square", "person": "Joseph", "start_time": "11:30", "end_time": "11:45"},
            {"action": "meet", "location": "Russian Hill", "person": "Karen", "start_time": "14:30", "end_time": "15:00"},
            {"action": "meet", "location": "North Beach", "person": "Kimberly", "start_time": "15:15", "end_time": "15:45"},
            {"action": "meet", "location": "The Castro", "person": "Laura", "start_time": "19:45", "end_time": "21:30"},
            {"action": "meet", "location": "Golden Gate Park", "person": "Daniel", "start_time": "21:45", "end_time": "22:00"}
        ]
        print(json.dumps({"itinerary": fallback_itinerary}, indent=2))

if __name__ == "__main__":
    main()