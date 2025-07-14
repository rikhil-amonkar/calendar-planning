from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the locations and friends
    locations = ['Chinatown', 'Mission District', 'Alamo Square', 'Pacific Heights', 
                 'Union Square', 'Golden Gate Park', 'Sunset District', 'Presidio']
    friends = {
        'David': {'location': 'Mission District', 'start': 8*60, 'end': 19*60 + 45, 'duration': 45},
        'Kenneth': {'location': 'Alamo Square', 'start': 14*60, 'end': 19*60 + 45, 'duration': 120},
        'John': {'location': 'Pacific Heights', 'start': 17*60, 'end': 20*60, 'duration': 15},
        'Deborah': {'location': 'Golden Gate Park', 'start': 7*60, 'end': 18*60 + 15, 'duration': 90},
        'Karen': {'location': 'Sunset District', 'start': 17*60 + 45, 'end': 21*60 + 15, 'duration': 15},
        'Carol': {'location': 'Presidio', 'start': 8*60 + 15, 'end': 9*60 + 15, 'duration': 30},
        'Charles': {'location': 'Union Square', 'start': 21*60 + 45, 'end': 22*60 + 45, 'duration': 60}
    }

    # Travel times matrix (in minutes)
    travel_times = {
        ('Chinatown', 'Mission District'): 18,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'Presidio'): 19,
        ('Mission District', 'Chinatown'): 16,
        ('Mission District', 'Alamo Square'): 11,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Presidio'): 25,
        ('Alamo Square', 'Chinatown'): 16,
        ('Alamo Square', 'Mission District'): 10,
        ('Alamo Square', 'Pacific Heights'): 10,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'Presidio'): 18,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Alamo Square'): 10,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Sunset District'): 21,
        ('Pacific Heights', 'Presidio'): 11,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Mission District'): 14,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Sunset District'): 26,
        ('Union Square', 'Presidio'): 24,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Mission District'): 24,
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Pacific Heights'): 21,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Presidio'): 16,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Mission District'): 26,
        ('Presidio', 'Alamo Square'): 18,
        ('Presidio', 'Pacific Heights'): 11,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Sunset District'): 15
    }

    # Variables for meeting start and end times
    meeting_start = {name: Int(f'start_{name}') for name in friends}
    meeting_end = {name: Int(f'end_{name}') for name in friends}

    # Current location starts at Chinatown at 9:00 AM (540 minutes)
    current_time = 540
    current_location = 'Chinatown'

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        s.add(meeting_start[name] >= friend['start'])
        s.add(meeting_end[name] <= friend['end'])
        s.add(meeting_end[name] == meeting_start[name] + friend['duration'])

    # Variables to indicate whether we meet each friend
    meet_friend = {name: Bool(f'meet_{name}') for name in friends}

    # We must meet exactly 6 friends
    s.add(Sum([If(meet_friend[name], 1, 0) for name in friends]) == 6)

    # Constraints for travel times and meeting order
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                # If we meet both name1 and name2, ensure travel time is accounted for
                s.add(Implies(And(meet_friend[name1], meet_friend[name2]),
                      Or(
                          meeting_start[name2] >= meeting_end[name1] + travel_times[(friends[name1]['location'], friends[name2]['location'])],
                          meeting_start[name1] >= meeting_end[name2] + travel_times[(friends[name2]['location'], friends[name1]['location'])]
                      ))

    # Ensure we start at Chinatown and account for initial travel time
    for name in friends:
        s.add(Implies(meet_friend[name],
                      meeting_start[name] >= current_time + travel_times[(current_location, friends[name]['location'])]))

    # Check if all constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        met_friends = [name for name in friends if m[meet_friend[name]]]
        for name in sorted(met_friends, key=lambda x: m[meeting_start[x]].as_long()):
            start = m[meeting_start[name]].as_long()
            end = m[meeting_end[name]].as_long()
            print(f"Meet {name} at {friends[name]['location']} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
    else:
        print("No valid schedule found.")

solve_scheduling()