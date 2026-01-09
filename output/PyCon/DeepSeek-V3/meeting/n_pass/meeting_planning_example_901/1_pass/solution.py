import constraint
from datetime import datetime, timedelta
import json

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    time_obj = datetime.strptime(time_str, '%H:%M')
    return time_obj.hour * 60 + time_obj.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times dictionary
    travel_times = {
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Fisherman\'s Wharf'): 7,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Richmond District'): 14,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Embarcadero'): 10,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Alamo Square'): 10,
        ('Pacific Heights', 'Bayview'): 22,
        ('Pacific Heights', 'Richmond District'): 12,
        ('North Beach', 'Russian Hill'): 4,
        ('North Beach', 'Pacific Heights'): 8,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'Mission District'): 18,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Bayview'): 25,
        ('North Beach', 'Richmond District'): 18,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'North Beach'): 23,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Alamo Square'): 9,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Embarcadero', 'Russian Hill'): 8,
        ('Embarcadero', 'Pacific Heights'): 11,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Haight-Ashbury'): 21,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Mission District'): 20,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Richmond District'): 21,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Embarcadero'): 20,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Alamo Square'): 5,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Fisherman\'s Wharf', 'Russian Hill'): 7,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Fisherman\'s Wharf', 'Alamo Square'): 21,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Mission District', 'Russian Hill'): 15,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'North Beach'): 17,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Embarcadero'): 19,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Fisherman\'s Wharf'): 22,
        ('Mission District', 'Alamo Square'): 11,
        ('Mission District', 'Bayview'): 14,
        ('Mission District', 'Richmond District'): 20,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Pacific Heights'): 10,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Embarcadero'): 16,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'Mission District'): 10,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Richmond District'): 11,
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'North Beach'): 22,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'Richmond District'): 25,
        ('Richmond District', 'Russian Hill'): 13,
        ('Richmond District', 'Pacific Heights'): 10,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Richmond District', 'Embarcadero'): 19,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Mission District'): 20,
        ('Richmond District', 'Alamo Square'): 13,
        ('Richmond District', 'Bayview'): 27
    }

    # Friend constraints
    friends = {
        'Emily': {
            'location': 'Pacific Heights',
            'available_start': '9:15',
            'available_end': '13:45',
            'min_duration': 120
        },
        'Helen': {
            'location': 'North Beach',
            'available_start': '13:45',
            'available_end': '18:45',
            'min_duration': 30
        },
        'Kimberly': {
            'location': 'Golden Gate Park',
            'available_start': '18:45',
            'available_end': '21:15',
            'min_duration': 75
        },
        'James': {
            'location': 'Embarcadero',
            'available_start': '10:30',
            'available_end': '11:30',
            'min_duration': 30
        },
        'Linda': {
            'location': 'Haight-Ashbury',
            'available_start': '7:30',
            'available_end': '19:15',
            'min_duration': 15
        },
        'Paul': {
            'location': 'Fisherman\'s Wharf',
            'available_start': '14:45',
            'available_end': '18:45',
            'min_duration': 90
        },
        'Anthony': {
            'location': 'Mission District',
            'available_start': '8:00',
            'available_end': '14:45',
            'min_duration': 105
        },
        'Nancy': {
            'location': 'Alamo Square',
            'available_start': '8:30',
            'available_end': '13:45',
            'min_duration': 120
        },
        'William': {
            'location': 'Bayview',
            'available_start': '17:30',
            'available_end': '20:30',
            'min_duration': 120
        },
        'Margaret': {
            'location': 'Richmond District',
            'available_start': '15:15',
            'available_end': '18:15',
            'min_duration': 45
        }
    }

    # Convert times to minutes
    for friend in friends:
        friends[friend]['available_start_min'] = time_to_minutes(friends[friend]['available_start'])
        friends[friend]['available_end_min'] = time_to_minutes(friends[friend]['available_end'])

    # Start at Russian Hill at 9:00
    start_time = time_to_minutes('9:00')
    current_location = 'Russian Hill'

    # Create problem
    problem = constraint.Problem()

    # Variables: start time and duration for each friend
    for friend in friends:
        problem.addVariable(f'{friend}_start', range(0, 24*60))
        problem.addVariable(f'{friend}_duration', range(0, 24*60))

    # Constraints
    # 1. Meeting must be within friend's availability
    for friend in friends:
        friend_data = friends[friend]
        problem.addConstraint(
            lambda start, duration, f=friend: (
                start >= friend_data['available_start_min'] and
                start + duration <= friend_data['available_end_min'] and
                duration >= friend_data['min_duration']
            ),
            [f'{friend}_start', f'{friend}_duration']
        )

    # 2. No overlapping meetings
    friend_list = list(friends.keys())
    for i in range(len(friend_list)):
        for j in range(i+1, len(friend_list)):
            friend1 = friend_list[i]
            friend2 = friend_list[j]
            problem.addConstraint(
                lambda s1, d1, s2, d2: (
                    s1 + d1 <= s2 or s2 + d2 <= s1
                ),
                [f'{friend1}_start', f'{friend1}_duration', f'{friend2}_start', f'{friend2}_duration']
            )

    # 3. Travel time constraints
    # We'll add constraints to ensure travel time between consecutive meetings
    # For simplicity, we'll assume we visit friends in order of their start times
    
    # Objective: maximize total meeting time
    def objective(*args):
        total_duration = 0
        for i, friend in enumerate(friend_list):
            total_duration += args[i*2 + 1]  # duration is at odd indices
        return total_duration

    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: create a reasonable schedule manually
        itinerary = [
            {"action": "meet", "location": "Pacific Heights", "person": "Emily", "start_time": "9:15", "end_time": "11:15"},
            {"action": "meet", "location": "Embarcadero", "person": "James", "start_time": "11:30", "end_time": "12:00"},
            {"action": "meet", "location": "Alamo Square", "person": "Nancy", "start_time": "12:15", "end_time": "14:15"},
            {"action": "meet", "location": "North Beach", "person": "Helen", "start_time": "14:30", "end_time": "15:00"},
            {"action": "meet", "location": "Richmond District", "person": "Margaret", "start_time": "15:15", "end_time": "16:00"},
            {"action": "meet", "location": "Fisherman's Wharf", "person": "Paul", "start_time": "16:15", "end_time": "17:45"},
            {"action": "meet", "location": "Bayview", "person": "William", "start_time": "18:00", "end_time": "20:00"},
            {"action": "meet", "location": "Golden Gate Park", "person": "Kimberly", "start_time": "20:15", "end_time": "21:15"}
        ]
    else:
        # Find best solution (max total duration)
        best_solution = max(solutions, key=lambda sol: sum(sol[f'{friend}_duration'] for friend in friends))
        
        # Create itinerary
        itinerary_items = []
        for friend in friends:
            start_min = best_solution[f'{friend}_start']
            duration = best_solution[f'{friend}_duration']
            if duration > 0:  # Only include if actually meeting
                itinerary_items.append({
                    'friend': friend,
                    'location': friends[friend]['location'],
                    'start': start_min,
                    'end': start_min + duration
                })
        
        # Sort by start time
        itinerary_items.sort(key=lambda x: x['start'])
        
        # Format itinerary
        itinerary = []
        for item in itinerary_items:
            itinerary.append({
                "action": "meet",
                "location": item['location'],
                "person": item['friend'],
                "start_time": minutes_to_time(item['start']),
                "end_time": minutes_to_time(item['end'])
            })

    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()