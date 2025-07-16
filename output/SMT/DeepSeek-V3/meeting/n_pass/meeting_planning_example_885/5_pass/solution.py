from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Optimize()

    # Define friends and their availability
    friends = {
        'Mark': {'location': 'Marina District', 'start': 18.75, 'end': 21.0, 'min_duration': 1.5},
        'Karen': {'location': 'Financial District', 'start': 9.5, 'end': 12.75, 'min_duration': 1.5},
        'Barbara': {'location': 'Alamo Square', 'start': 10.0, 'end': 19.5, 'min_duration': 1.5},
        'Nancy': {'location': 'Golden Gate Park', 'start': 16.75, 'end': 20.0, 'min_duration': 1.75},
        'David': {'location': 'The Castro', 'start': 9.0, 'end': 18.0, 'min_duration': 2.0},
        'Linda': {'location': 'Bayview', 'start': 18.25, 'end': 19.75, 'min_duration': 0.75},
        'Kevin': {'location': 'Sunset District', 'start': 10.0, 'end': 17.75, 'min_duration': 2.0},
        'Matthew': {'location': 'Haight-Ashbury', 'start': 10.25, 'end': 15.5, 'min_duration': 0.75},
        'Andrew': {'location': 'Nob Hill', 'start': 11.75, 'end': 16.75, 'min_duration': 1.75}
    }

    # Complete travel times (in hours)
    travel_times = {
        ('Russian Hill', 'Marina District'): 7/60,
        ('Russian Hill', 'Financial District'): 11/60,
        ('Russian Hill', 'Alamo Square'): 15/60,
        ('Russian Hill', 'Golden Gate Park'): 21/60,
        ('Russian Hill', 'The Castro'): 21/60,
        ('Russian Hill', 'Bayview'): 23/60,
        ('Russian Hill', 'Sunset District'): 23/60,
        ('Russian Hill', 'Haight-Ashbury'): 17/60,
        ('Russian Hill', 'Nob Hill'): 5/60,
        ('Marina District', 'Russian Hill'): 8/60,
        ('Marina District', 'Financial District'): 17/60,
        ('Marina District', 'Alamo Square'): 15/60,
        ('Marina District', 'Golden Gate Park'): 18/60,
        ('Marina District', 'The Castro'): 22/60,
        ('Marina District', 'Bayview'): 27/60,
        ('Marina District', 'Sunset District'): 19/60,
        ('Marina District', 'Haight-Ashbury'): 16/60,
        ('Marina District', 'Nob Hill'): 12/60,
        ('Financial District', 'Russian Hill'): 11/60,
        ('Financial District', 'Marina District'): 15/60,
        ('Financial District', 'Alamo Square'): 17/60,
        ('Financial District', 'Golden Gate Park'): 23/60,
        ('Financial District', 'The Castro'): 20/60,
        ('Financial District', 'Bayview'): 19/60,
        ('Financial District', 'Sunset District'): 30/60,
        ('Financial District', 'Haight-Ashbury'): 19/60,
        ('Financial District', 'Nob Hill'): 8/60,
        ('Alamo Square', 'Russian Hill'): 13/60,
        ('Alamo Square', 'Marina District'): 15/60,
        ('Alamo Square', 'Financial District'): 17/60,
        ('Alamo Square', 'Golden Gate Park'): 9/60,
        ('Alamo Square', 'The Castro'): 8/60,
        ('Alamo Square', 'Bayview'): 16/60,
        ('Alamo Square', 'Sunset District'): 16/60,
        ('Alamo Square', 'Haight-Ashbury'): 5/60,
        ('Alamo Square', 'Nob Hill'): 11/60,
        ('Golden Gate Park', 'Russian Hill'): 19/60,
        ('Golden Gate Park', 'Marina District'): 16/60,
        ('Golden Gate Park', 'Financial District'): 26/60,
        ('Golden Gate Park', 'Alamo Square'): 9/60,
        ('Golden Gate Park', 'The Castro'): 13/60,
        ('Golden Gate Park', 'Bayview'): 23/60,
        ('Golden Gate Park', 'Sunset District'): 10/60,
        ('Golden Gate Park', 'Haight-Ashbury'): 7/60,
        ('Golden Gate Park', 'Nob Hill'): 20/60,
        ('The Castro', 'Russian Hill'): 18/60,
        ('The Castro', 'Marina District'): 21/60,
        ('The Castro', 'Financial District'): 21/60,
        ('The Castro', 'Alamo Square'): 8/60,
        ('The Castro', 'Golden Gate Park'): 11/60,
        ('The Castro', 'Bayview'): 19/60,
        ('The Castro', 'Sunset District'): 17/60,
        ('The Castro', 'Haight-Ashbury'): 6/60,
        ('The Castro', 'Nob Hill'): 16/60,
        ('Bayview', 'Russian Hill'): 23/60,
        ('Bayview', 'Marina District'): 27/60,
        ('Bayview', 'Financial District'): 19/60,
        ('Bayview', 'Alamo Square'): 16/60,
        ('Bayview', 'Golden Gate Park'): 22/60,
        ('Bayview', 'The Castro'): 19/60,
        ('Bayview', 'Sunset District'): 23/60,
        ('Bayview', 'Haight-Ashbury'): 19/60,
        ('Bayview', 'Nob Hill'): 20/60,
        ('Sunset District', 'Russian Hill'): 24/60,
        ('Sunset District', 'Marina District'): 21/60,
        ('Sunset District', 'Financial District'): 30/60,
        ('Sunset District', 'Alamo Square'): 17/60,
        ('Sunset District', 'Golden Gate Park'): 11/60,
        ('Sunset District', 'The Castro'): 17/60,
        ('Sunset District', 'Bayview'): 22/60,
        ('Sunset District', 'Haight-Ashbury'): 15/60,
        ('Sunset District', 'Nob Hill'): 27/60,
        ('Haight-Ashbury', 'Russian Hill'): 17/60,
        ('Haight-Ashbury', 'Marina District'): 17/60,
        ('Haight-Ashbury', 'Financial District'): 21/60,
        ('Haight-Ashbury', 'Alamo Square'): 5/60,
        ('Haight-Ashbury', 'Golden Gate Park'): 7/60,
        ('Haight-Ashbury', 'The Castro'): 6/60,
        ('Haight-Ashbury', 'Bayview'): 18/60,
        ('Haight-Ashbury', 'Sunset District'): 15/60,
        ('Haight-Ashbury', 'Nob Hill'): 15/60,
        ('Nob Hill', 'Russian Hill'): 5/60,
        ('Nob Hill', 'Marina District'): 11/60,
        ('Nob Hill', 'Financial District'): 9/60,
        ('Nob Hill', 'Alamo Square'): 11/60,
        ('Nob Hill', 'Golden Gate Park'): 17/60,
        ('Nob Hill', 'The Castro'): 17/60,
        ('Nob Hill', 'Bayview'): 19/60,
        ('Nob Hill', 'Sunset District'): 24/60,
        ('Nob Hill', 'Haight-Ashbury'): 13/60,
    }

    # Create variables for meeting times
    meeting_start = {name: Real(f'start_{name}') for name in friends}
    meeting_end = {name: Real(f'end_{name}') for name in friends}

    # Starting point
    current_time = 9.0  # 9:00 AM
    current_location = 'Russian Hill'

    # Basic constraints for each meeting
    for name in friends:
        s.add(meeting_start[name] >= friends[name]['start'])
        s.add(meeting_end[name] <= friends[name]['end'])
        s.add(meeting_end[name] - meeting_start[name] >= friends[name]['min_duration'])

    # Create a list to track meeting order
    meeting_order = [name for name in friends]
    
    # Add travel time constraints between consecutive meetings
    for i in range(len(meeting_order)-1):
        current = meeting_order[i]
        next_meeting = meeting_order[i+1]
        travel_time = travel_times.get(
            (friends[current]['location'], friends[next_meeting]['location']), 0)
        s.add(meeting_start[next_meeting] >= meeting_end[current] + travel_time)

    # Maximize the number of friends met
    met = [If(And(meeting_start[name] >= friends[name]['start'],
               meeting_end[name] <= friends[name]['end'],
               meeting_end[name] - meeting_start[name] >= friends[name]['min_duration']), 1, 0)
           for name in friends]
    total_met = Sum(met)
    s.maximize(total_met)

    # Solve and print results
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        scheduled = []
        for name in friends:
            start_val = m[meeting_start[name]]
            end_val = m[meeting_end[name]]
            if is_true(m.evaluate(met[list(friends.keys()).index(name)] == 1)):
                start = float(start_val.numerator_as_long())/float(start_val.denominator_as_long())
                end = float(end_val.numerator_as_long())/float(end_val.denominator_as_long())
                scheduled.append((start, name))
                print(f"Meet {name} at {friends[name]['location']} from {start:.2f} to {end:.2f}")
        
        # Print in chronological order
        print("\nChronological Order:")
        for time, name in sorted(scheduled):
            print(f"{time:.2f}: Meet {name} at {friends[name]['location']}")
        
        print(f"\nTotal friends met: {m.evaluate(total_met)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()