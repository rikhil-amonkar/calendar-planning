from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (0 minutes)
    # Friends' availability windows in minutes since 9:00 AM
    # Andrew: Golden Gate Park, 11:45AM (165 mins) to 2:30PM (330 mins)
    andrew_start = 165
    andrew_end = 330
    # Sarah: Pacific Heights, 4:15PM (435 mins) to 6:45PM (525 mins)
    sarah_start = 435
    sarah_end = 525
    # Nancy: Presidio, 5:30PM (510 mins) to 7:15PM (555 mins)
    nancy_start = 510
    nancy_end = 555
    # Rebecca: Chinatown, 9:45AM (45 mins) to 9:30PM (750 mins)
    rebecca_start = 45
    rebecca_end = 750
    # Robert: The Castro, 8:30AM (-30 mins) to 2:15PM (315 mins)
    # Adjusted to start at 9:00 AM (0 mins) since we arrive at 9:00 AM
    robert_start = 0
    robert_end = 315

    # Meeting durations in minutes
    andrew_min_duration = 75
    sarah_min_duration = 15
    nancy_min_duration = 60
    rebecca_min_duration = 90
    robert_min_duration = 30

    # Variables for start and end times of each meeting
    andrew_meet_start = Real('andrew_meet_start')
    andrew_meet_end = Real('andrew_meet_end')
    sarah_meet_start = Real('sarah_meet_start')
    sarah_meet_end = Real('sarah_meet_end')
    nancy_meet_start = Real('nancy_meet_start')
    nancy_meet_end = Real('nancy_meet_end')
    rebecca_meet_start = Real('rebecca_meet_start')
    rebecca_meet_end = Real('rebecca_meet_end')
    robert_meet_start = Real('robert_meet_start')
    robert_meet_end = Real('robert_meet_end')

    # Constraints for each meeting's duration and availability
    # Andrew
    s.add(andrew_meet_start >= andrew_start)
    s.add(andrew_meet_end <= andrew_end)
    s.add(andrew_meet_end - andrew_meet_start >= andrew_min_duration)
    # Sarah
    s.add(sarah_meet_start >= sarah_start)
    s.add(sarah_meet_end <= sarah_end)
    s.add(sarah_meet_end - sarah_meet_start >= sarah_min_duration)
    # Nancy
    s.add(nancy_meet_start >= nancy_start)
    s.add(nancy_meet_end <= nancy_end)
    s.add(nancy_meet_end - nancy_meet_start >= nancy_min_duration)
    # Rebecca
    s.add(rebecca_meet_start >= rebecca_start)
    s.add(rebecca_meet_end <= rebecca_end)
    s.add(rebecca_meet_end - rebecca_meet_start >= rebecca_min_duration)
    # Robert
    s.add(robert_meet_start >= robert_start)
    s.add(robert_meet_end <= robert_end)
    s.add(robert_meet_end - robert_meet_start >= robert_min_duration)

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Union Square': {
            'Golden Gate Park': 22,
            'Pacific Heights': 15,
            'Presidio': 24,
            'Chinatown': 7,
            'The Castro': 19
        },
        'Golden Gate Park': {
            'Union Square': 22,
            'Pacific Heights': 16,
            'Presidio': 11,
            'Chinatown': 23,
            'The Castro': 13
        },
        'Pacific Heights': {
            'Union Square': 12,
            'Golden Gate Park': 15,
            'Presidio': 11,
            'Chinatown': 11,
            'The Castro': 16
        },
        'Presidio': {
            'Union Square': 22,
            'Golden Gate Park': 12,
            'Pacific Heights': 11,
            'Chinatown': 21,
            'The Castro': 21
        },
        'Chinatown': {
            'Union Square': 7,
            'Golden Gate Park': 23,
            'Pacific Heights': 10,
            'Presidio': 19,
            'The Castro': 22
        },
        'The Castro': {
            'Union Square': 19,
            'Golden Gate Park': 11,
            'Pacific Heights': 16,
            'Presidio': 20,
            'Chinatown': 20
        }
    }

    # Locations of each friend
    friend_locations = {
        'Andrew': 'Golden Gate Park',
        'Sarah': 'Pacific Heights',
        'Nancy': 'Presidio',
        'Rebecca': 'Chinatown',
        'Robert': 'The Castro'
    }

    # Assume an order of visiting friends: Robert -> Rebecca -> Andrew -> Sarah -> Nancy
    # Start at Union Square at time 0
    # Travel to Robert at The Castro: 19 mins
    s.add(robert_meet_start >= 19)
    # After Robert, travel to Rebecca at Chinatown: 20 mins
    s.add(rebecca_meet_start >= robert_meet_end + travel_times['The Castro']['Chinatown'])
    # After Rebecca, travel to Andrew at Golden Gate Park: 23 mins
    s.add(andrew_meet_start >= rebecca_meet_end + travel_times['Chinatown']['Golden Gate Park'])
    # After Andrew, travel to Sarah at Pacific Heights: 16 mins
    s.add(sarah_meet_start >= andrew_meet_end + travel_times['Golden Gate Park']['Pacific Heights'])
    # After Sarah, travel to Nancy at Presidio: 11 mins
    s.add(nancy_meet_start >= sarah_meet_end + travel_times['Pacific Heights']['Presidio'])

    # Check if the schedule is feasible
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found:")
        # Convert minutes back to time format for readability
        def minutes_to_time(minutes):
            hours = int(minutes) // 60
            mins = int(minutes) % 60
            return f"{9 + hours}:{mins:02d} {'AM' if hours < 3 else 'PM'}"

        print(f"Meet Robert at The Castro: from {minutes_to_time(m[robert_meet_start].as_long())} to {minutes_to_time(m[robert_meet_end].as_long())}")
        print(f"Meet Rebecca at Chinatown: from {minutes_to_time(m[rebecca_meet_start].as_long())} to {minutes_to_time(m[rebecca_meet_end].as_long())}")
        print(f"Meet Andrew at Golden Gate Park: from {minutes_to_time(m[andrew_meet_start].as_long())} to {minutes_to_time(m[andrew_meet_end].as_long())}")
        print(f"Meet Sarah at Pacific Heights: from {minutes_to_time(m[sarah_meet_start].as_long())} to {minutes_to_time(m[sarah_meet_end].as_long())}")
        print(f"Meet Nancy at Presidio: from {minutes_to_time(m[nancy_meet_start].as_long())} to {minutes_to_time(m[nancy_meet_end].as_long())}")
    else:
        print("No feasible schedule found with the assumed order.")

solve_scheduling()