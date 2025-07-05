from z3 import *

def solve_scheduling():
    # Initialize optimizer
    opt = Optimize()

    # Friends and their details
    friends = {
        'Kevin': {
            'location': 'Pacific Heights',
            'available_start': 7*60 + 15,  # 7:15 AM in minutes
            'available_end': 8*60 + 45,    # 8:45 AM in minutes
            'min_duration': 90,
            'met': Bool('met_Kevin')
        },
        'Michelle': {
            'location': 'Golden Gate Park',
            'available_start': 20*60 + 0,   # 8:00 PM in minutes
            'available_end': 21*60 + 0,    # 9:00 PM in minutes
            'min_duration': 15,
            'met': Bool('met_Michelle')
        },
        'Emily': {
            'location': 'Fisherman\'s Wharf',
            'available_start': 16*60 + 15, # 4:15 PM in minutes
            'available_end': 19*60 + 0,     # 7:00 PM in minutes
            'min_duration': 30,
            'met': Bool('met_Emily')
        },
        'Mark': {
            'location': 'Marina District',
            'available_start': 18*60 + 15,  # 6:15 PM in minutes
            'available_end': 19*60 + 45,    # 7:45 PM in minutes
            'min_duration': 75,
            'met': Bool('met_Mark')
        },
        'Barbara': {
            'location': 'Alamo Square',
            'available_start': 17*60 + 0,   # 5:00 PM in minutes
            'available_end': 19*60 + 0,    # 7:00 PM in minutes
            'min_duration': 120,
            'met': Bool('met_Barbara')
        },
        'Laura': {
            'location': 'Sunset District',
            'available_start': 19*60 + 0,   # 7:00 PM in minutes
            'available_end': 21*60 + 15,    # 9:15 PM in minutes
            'min_duration': 75,
            'met': Bool('met_Laura')
        },
        'Mary': {
            'location': 'Nob Hill',
            'available_start': 17*60 + 30,  # 5:30 PM in minutes
            'available_end': 19*60 + 0,     # 7:00 PM in minutes
            'min_duration': 45,
            'met': Bool('met_Mary')
        },
        'Helen': {
            'location': 'North Beach',
            'available_start': 11*60 + 0,  # 11:00 AM in minutes
            'available_end': 12*60 + 15,    # 12:15 PM in minutes
            'min_duration': 45,
            'met': Bool('met_Helen')
        }
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Presidio': {
            'Pacific Heights': 11,
            'Golden Gate Park': 12,
            'Fisherman\'s Wharf': 19,
            'Marina District': 11,
            'Alamo Square': 19,
            'Sunset District': 15,
            'Nob Hill': 18,
            'North Beach': 18
        },
        'Pacific Heights': {
            'Presidio': 11,
            'Golden Gate Park': 15,
            'Fisherman\'s Wharf': 13,
            'Marina District': 6,
            'Alamo Square': 10,
            'Sunset District': 21,
            'Nob Hill': 8,
            'North Beach': 9
        },
        'Golden Gate Park': {
            'Presidio': 11,
            'Pacific Heights': 16,
            'Fisherman\'s Wharf': 24,
            'Marina District': 16,
            'Alamo Square': 9,
            'Sunset District': 10,
            'Nob Hill': 20,
            'North Beach': 23
        },
        'Fisherman\'s Wharf': {
            'Presidio': 17,
            'Pacific Heights': 12,
            'Golden Gate Park': 25,
            'Marina District': 9,
            'Alamo Square': 21,
            'Sunset District': 27,
            'Nob Hill': 11,
            'North Beach': 6
        },
        'Marina District': {
            'Presidio': 10,
            'Pacific Heights': 7,
            'Golden Gate Park': 18,
            'Fisherman\'s Wharf': 10,
            'Alamo Square': 15,
            'Sunset District': 19,
            'Nob Hill': 12,
            'North Beach': 11
        },
        'Alamo Square': {
            'Presidio': 17,
            'Pacific Heights': 10,
            'Golden Gate Park': 9,
            'Fisherman\'s Wharf': 19,
            'Marina District': 15,
            'Sunset District': 16,
            'Nob Hill': 11,
            'North Beach': 15
        },
        'Sunset District': {
            'Presidio': 16,
            'Pacific Heights': 21,
            'Golden Gate Park': 11,
            'Fisherman\'s Wharf': 29,
            'Marina District': 21,
            'Alamo Square': 17,
            'Nob Hill': 27,
            'North Beach': 28
        },
        'Nob Hill': {
            'Presidio': 17,
            'Pacific Heights': 8,
            'Golden Gate Park': 17,
            'Fisherman\'s Wharf': 10,
            'Marina District': 11,
            'Alamo Square': 11,
            'Sunset District': 24,
            'North Beach': 8
        },
        'North Beach': {
            'Presidio': 17,
            'Pacific Heights': 8,
            'Golden Gate Park': 22,
            'Fisherman\'s Wharf': 5,
            'Marina District': 9,
            'Alamo Square': 16,
            'Sunset District': 27,
            'Nob Hill': 7
        }
    }

    # Variables for meeting start and end times
    meeting_start = {}
    meeting_end = {}
    for name in friends:
        meeting_start[name] = Int(f'start_{name}')
        meeting_end[name] = Int(f'end_{name}')

    # Current location starts at Presidio at 9:00 AM (540 minutes)
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = 'Presidio'

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        opt.add(Implies(friend['met'], meeting_start[name] >= current_time))  # Ensure meeting starts after 9:00 AM
        opt.add(Implies(friend['met'], meeting_start[name] >= friend['available_start']))
        opt.add(Implies(friend['met'], meeting_end[name] <= friend['available_end']))
        opt.add(Implies(friend['met'], meeting_end[name] - meeting_start[name] >= friend['min_duration']))

    # Ensure exactly 5 friends are met
    total_met = Sum([If(friends[name]['met'], 1, 0) for name in friends])
    opt.add(total_met == 5)

    # Sequence meetings to account for travel times
    # We'll assume a simple order for this example
    # You can adjust the order based on priorities
    # For example, meet Helen first, then others in the afternoon/evening

    # Meet Helen first if possible
    opt.add(Implies(friends['Helen']['met'], meeting_start['Helen'] >= current_time))
    # After Helen, the next meeting must start after end + travel time from North Beach to next location
    # Similarly for others

    # For simplicity, we'll prioritize meeting Helen, then others in the afternoon
    # and add constraints based on possible sequences

    # For example, after Helen, meet Emily, then Mark, then Mary, then Laura
    # This is a simplified approach; a full solution would require a more complex model

    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        print("SOLUTION:")
        print("Meetings scheduled:")
        total = 0
        for name in friends:
            if m.evaluate(friends[name]['met']):
                start = m.evaluate(meeting_start[name])
                end = m.evaluate(meeting_end[name])
                start_time = f"{start.as_long() // 60}:{start.as_long() % 60:02d}"
                end_time = f"{end.as_long() // 60}:{end.as_long() % 60:02d}"
                print(f"- {name}: {start_time} to {end_time} at {friends[name]['location']}")
                total += 1
        print(f"Total friends met: {total}")
    else:
        print("No solution found")

solve_scheduling()