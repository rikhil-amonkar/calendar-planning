from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define travel times between locations (in minutes)
    travel_times = {
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Alamo Square'): 5,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
        ('Fisherman\'s Wharf', 'The Castro'): 26,
        ('Fisherman\'s Wharf', 'Chinatown'): 12,
        ('Fisherman\'s Wharf', 'Alamo Square'): 20,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Fisherman\'s Wharf', 'Russian Hill'): 7,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('The Castro', 'Fisherman\'s Wharf'): 24,
        ('The Castro', 'Chinatown'): 20,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Russian Hill'): 18,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'Fisherman\'s Wharf'): 8,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Russian Hill'): 7,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Chinatown'): 16,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Russian Hill'): 13,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'The Castro'): 22,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Russian Hill'): 4,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Fisherman\'s Wharf'): 7,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'North Beach'): 5,
    }

    # Define friends and their constraints
    friends = {
        'Carol': {
            'location': 'Haight-Ashbury',
            'available_start': 21 * 60 + 30,  # 9:30 PM in minutes
            'available_end': 22 * 60 + 30,    # 10:30 PM in minutes
            'duration': 60,                   # 60 minutes
        },
        'Laura': {
            'location': 'Fisherman\'s Wharf',
            'available_start': 11 * 60 + 45,  # 11:45 AM in minutes
            'available_end': 21 * 60 + 30,    # 9:30 PM in minutes
            'duration': 60,                   # 60 minutes
        },
        'Karen': {
            'location': 'The Castro',
            'available_start': 7 * 60 + 15,   # 7:15 AM in minutes
            'available_end': 14 * 60 + 0,     # 2:00 PM in minutes
            'duration': 75,                   # 75 minutes
        },
        'Elizabeth': {
            'location': 'Chinatown',
            'available_start': 12 * 60 + 15, # 12:15 PM in minutes
            'available_end': 21 * 60 + 30,    # 9:30 PM in minutes
            'duration': 75,                   # 75 minutes
        },
        'Deborah': {
            'location': 'Alamo Square',
            'available_start': 12 * 60 + 0,   # 12:00 PM in minutes
            'available_end': 15 * 60 + 0,     # 3:00 PM in minutes
            'duration': 105,                  # 105 minutes
        },
        'Jason': {
            'location': 'North Beach',
            'available_start': 14 * 60 + 45,  # 2:45 PM in minutes
            'available_end': 19 * 60 + 0,     # 7:00 PM in minutes
            'duration': 90,                   # 90 minutes
        },
        'Steven': {
            'location': 'Russian Hill',
            'available_start': 14 * 60 + 45,  # 2:45 PM in minutes
            'available_end': 18 * 60 + 30,    # 6:30 PM in minutes
            'duration': 120,                  # 120 minutes
        }
    }

    # Create variables for each friend's meeting start and end times
    meeting_vars = {}
    for friend in friends:
        start = Int(f'start_{friend}')
        end = Int(f'end_{friend}')
        meeting_vars[friend] = {'start': start, 'end': end}

    # Current location starts at Golden Gate Park at 9:00 AM (540 minutes)
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = 'Golden Gate Park'

    # Constraints for each friend's meeting
    for friend, data in friends.items():
        start = meeting_vars[friend]['start']
        end = meeting_vars[friend]['end']
        duration = data['duration']
        available_start = data['available_start']
        available_end = data['available_end']

        # Meeting must start and end within the friend's availability
        s.add(start >= available_start)
        s.add(end <= available_end)
        s.add(end == start + duration)

    # Create a list of friend names for easy access
    friend_names = list(friends.keys())
    num_friends = len(friend_names)

    # Create variables to represent the order of meetings
    # We'll use a list of integers where each represents the position of a friend in the schedule
    position = {friend: Int(f'pos_{friend}') for friend in friend_names}
    # Each position must be between 0 and num_friends-1
    for friend in friend_names:
        s.add(position[friend] >= 0)
        s.add(position[friend] < num_friends)
    # All positions must be distinct
    s.add(Distinct([position[friend] for friend in friend_names]))

    # Add constraints for travel time between consecutive meetings
    for i in range(num_friends):
        for j in range(num_friends):
            if i != j:
                # If friend i comes immediately before friend j in the schedule
                comes_before = And(position[friend_names[i]] + 1 == position[friend_names[j]])
                # Then the start time of j must be >= end time of i + travel time
                travel_time = travel_times[(friends[friend_names[i]]['location'], friends[friend_names[j]]['location'])]
                s.add(Implies(comes_before, 
                             meeting_vars[friend_names[j]]['start'] >= meeting_vars[friend_names[i]]['end'] + travel_time))

    # Add constraint for the first meeting (must be reachable from starting location)
    for friend in friend_names:
        travel_time = travel_times[(current_location, friends[friend]['location'])]
        s.add(Implies(position[friend] == 0, 
                     meeting_vars[friend]['start'] >= current_time + travel_time))

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        # Get the schedule order
        schedule_order = sorted(friend_names, key=lambda x: model[position[x]].as_long())
        # Build the itinerary
        itinerary = []
        for friend in schedule_order:
            start_val = model[meeting_vars[friend]['start']].as_long()
            end_val = model[meeting_vars[friend]['end']].as_long()
            start_hh = start_val // 60
            start_mm = start_val % 60
            end_hh = end_val // 60
            end_mm = end_val % 60
            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": f"{start_hh:02d}:{start_mm:02d}",
                "end_time": f"{end_hh:02d}:{end_mm:02d}"
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))