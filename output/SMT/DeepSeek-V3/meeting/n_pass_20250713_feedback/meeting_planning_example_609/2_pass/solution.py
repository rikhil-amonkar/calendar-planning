from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the locations and friends (excluding Charles)
    locations = ['Chinatown', 'Mission District', 'Alamo Square', 'Pacific Heights', 
                 'Union Square', 'Golden Gate Park', 'Sunset District', 'Presidio']
    friends = {
        'David': {'location': 'Mission District', 'start': 8*60, 'end': 19*60 + 45, 'duration': 45},
        'Kenneth': {'location': 'Alamo Square', 'start': 14*60, 'end': 19*60 + 45, 'duration': 120},
        'John': {'location': 'Pacific Heights', 'start': 17*60, 'end': 20*60, 'duration': 15},
        'Deborah': {'location': 'Golden Gate Park', 'start': 7*60, 'end': 18*60 + 15, 'duration': 90},
        'Karen': {'location': 'Sunset District', 'start': 17*60 + 45, 'end': 21*60 + 15, 'duration': 15},
        'Carol': {'location': 'Presidio', 'start': 8*60 + 15, 'end': 9*60 + 15, 'duration': 30}
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

    # Order of meetings and travel times
    # We'll try to meet Carol first (early availability), then David, Deborah, Kenneth, John, and Karen.
    # This is a heuristic; a more complex solution would let Z3 decide the order.

    # Meet Carol at Presidio
    s.add(meeting_start['Carol'] >= current_time + travel_times[(current_location, 'Presidio')])
    s.add(meeting_start['Carol'] <= friends['Carol']['end'] - friends['Carol']['duration'])
    current_time_after_carol = meeting_end['Carol']
    current_location_after_carol = 'Presidio'

    # Meet David at Mission District
    s.add(meeting_start['David'] >= current_time_after_carol + travel_times[(current_location_after_carol, 'Mission District')])
    s.add(meeting_start['David'] <= friends['David']['end'] - friends['David']['duration'])
    current_time_after_david = meeting_end['David']
    current_location_after_david = 'Mission District'

    # Meet Deborah at Golden Gate Park
    s.add(meeting_start['Deborah'] >= current_time_after_david + travel_times[(current_location_after_david, 'Golden Gate Park')])
    s.add(meeting_start['Deborah'] <= friends['Deborah']['end'] - friends['Deborah']['duration'])
    current_time_after_deborah = meeting_end['Deborah']
    current_location_after_deborah = 'Golden Gate Park'

    # Meet Kenneth at Alamo Square
    s.add(meeting_start['Kenneth'] >= current_time_after_deborah + travel_times[(current_location_after_deborah, 'Alamo Square')])
    s.add(meeting_start['Kenneth'] >= friends['Kenneth']['start'])
    s.add(meeting_start['Kenneth'] <= friends['Kenneth']['end'] - friends['Kenneth']['duration'])
    current_time_after_kenneth = meeting_end['Kenneth']
    current_location_after_kenneth = 'Alamo Square'

    # Meet John at Pacific Heights
    s.add(meeting_start['John'] >= current_time_after_kenneth + travel_times[(current_location_after_kenneth, 'Pacific Heights')])
    s.add(meeting_start['John'] >= friends['John']['start'])
    s.add(meeting_start['John'] <= friends['John']['end'] - friends['John']['duration'])
    current_time_after_john = meeting_end['John']
    current_location_after_john = 'Pacific Heights'

    # Meet Karen at Sunset District
    s.add(meeting_start['Karen'] >= current_time_after_john + travel_times[(current_location_after_john, 'Sunset District')])
    s.add(meeting_start['Karen'] >= friends['Karen']['start'])
    s.add(meeting_start['Karen'] <= friends['Karen']['end'] - friends['Karen']['duration'])

    # Check if all constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        for name in friends:
            start = m[meeting_start[name]].as_long()
            end = m[meeting_end[name]].as_long()
            print(f"Meet {name} at {friends[name]['location']} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
    else:
        print("No valid schedule found.")

solve_scheduling()