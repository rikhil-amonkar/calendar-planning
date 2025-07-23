from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Locations and friends
    locations = ['Haight-Ashbury', 'Mission District', 'Bayview', 'Pacific Heights', 'Russian Hill', 'Fisherman\'s Wharf']
    friends = {
        'Stephanie': {'location': 'Mission District', 'start': 8.25, 'end': 13.75, 'duration': 1.5},
        'Sandra': {'location': 'Bayview', 'start': 13.0, 'end': 19.5, 'duration': 0.25},
        'Richard': {'location': 'Pacific Heights', 'start': 7.25, 'end': 10.25, 'duration': 1.25},
        'Brian': {'location': 'Russian Hill', 'start': 12.25, 'end': 16.0, 'duration': 2.0},
        'Jason': {'location': 'Fisherman\'s Wharf', 'start': 8.5, 'end': 17.75, 'duration': 1.0}
    }

    # Travel times (in hours)
    travel_times = {
        ('Haight-Ashbury', 'Mission District'): 11/60,
        ('Haight-Ashbury', 'Bayview'): 18/60,
        ('Haight-Ashbury', 'Pacific Heights'): 12/60,
        ('Haight-Ashbury', 'Russian Hill'): 17/60,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23/60,
        ('Mission District', 'Haight-Ashbury'): 12/60,
        ('Mission District', 'Bayview'): 15/60,
        ('Mission District', 'Pacific Heights'): 16/60,
        ('Mission District', 'Russian Hill'): 15/60,
        ('Mission District', 'Fisherman\'s Wharf'): 22/60,
        ('Bayview', 'Haight-Ashbury'): 19/60,
        ('Bayview', 'Mission District'): 13/60,
        ('Bayview', 'Pacific Heights'): 23/60,
        ('Bayview', 'Russian Hill'): 23/60,
        ('Bayview', 'Fisherman\'s Wharf'): 25/60,
        ('Pacific Heights', 'Haight-Ashbury'): 11/60,
        ('Pacific Heights', 'Mission District'): 15/60,
        ('Pacific Heights', 'Bayview'): 22/60,
        ('Pacific Heights', 'Russian Hill'): 7/60,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13/60,
        ('Russian Hill', 'Haight-Ashbury'): 17/60,
        ('Russian Hill', 'Mission District'): 16/60,
        ('Russian Hill', 'Bayview'): 23/60,
        ('Russian Hill', 'Pacific Heights'): 7/60,
        ('Russian Hill', 'Fisherman\'s Wharf'): 7/60,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22/60,
        ('Fisherman\'s Wharf', 'Mission District'): 22/60,
        ('Fisherman\'s Wharf', 'Bayview'): 26/60,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12/60,
        ('Fisherman\'s Wharf', 'Russian Hill'): 7/60
    }

    # Variables for start and end times of each meeting
    meeting_start = {name: Real(f'start_{name}') for name in friends}
    meeting_end = {name: Real(f'end_{name}') for name in friends}

    # Current location starts at Haight-Ashbury at 9:00 AM
    current_time = 9.0
    current_location = 'Haight-Ashbury'

    # Order of meetings (to be determined by the solver)
    # We'll use a list to represent the sequence of meetings
    # For simplicity, we'll assume we can meet all friends, but the solver will enforce constraints

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        s.add(meeting_start[name] >= friend['start'])
        s.add(meeting_end[name] <= friend['end'])
        s.add(meeting_end[name] == meeting_start[name] + friend['duration'])

    # Travel constraints between meetings
    # We need to model the sequence of meetings and travel times
    # For simplicity, we'll assume we can meet all friends and enforce travel times between them
    # This is a simplified approach; a more complex model would involve sequencing variables

    # For now, we'll prioritize meeting Richard first (since his window is earliest)
    # Then Stephanie, then Brian, then Sandra, then Jason
    # This is a heuristic; the solver should ideally determine the optimal order

    # Meet Richard first
    s.add(meeting_start['Richard'] >= current_time + travel_times[(current_location, friends['Richard']['location'])])
    current_time = meeting_end['Richard']
    current_location = friends['Richard']['location']

    # Then meet Stephanie
    s.add(meeting_start['Stephanie'] >= current_time + travel_times[(current_location, friends['Stephanie']['location'])])
    current_time = meeting_end['Stephanie']
    current_location = friends['Stephanie']['location']

    # Then meet Brian
    s.add(meeting_start['Brian'] >= current_time + travel_times[(current_location, friends['Brian']['location'])])
    current_time = meeting_end['Brian']
    current_location = friends['Brian']['location']

    # Then meet Sandra
    s.add(meeting_start['Sandra'] >= current_time + travel_times[(current_location, friends['Sandra']['location'])])
    current_time = meeting_end['Sandra']
    current_location = friends['Sandra']['location']

    # Then meet Jason
    s.add(meeting_start['Jason'] >= current_time + travel_times[(current_location, friends['Jason']['location'])])
    current_time = meeting_end['Jason']
    current_location = friends['Jason']['location']

    # Check if all constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        for name in friends:
            start = m[meeting_start[name]].as_fraction()
            end = m[meeting_end[name]].as_fraction()
            print(f"Meet {name} at {friends[name]['location']} from {float(start):.2f} to {float(end):.2f}")
    else:
        print("No valid schedule found.")

solve_scheduling()