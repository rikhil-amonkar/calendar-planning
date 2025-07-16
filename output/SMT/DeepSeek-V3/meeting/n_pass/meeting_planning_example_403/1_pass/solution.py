from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
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
    robert_start = -30  # Not available before 9:00 AM, so adjusted to 9:00 AM (0)
    robert_end = 315

    # Meeting durations in minutes
    andrew_min_duration = 75
    sarah_min_duration = 15
    nancy_min_duration = 60
    rebecca_min_duration = 90
    robert_min_duration = 30

    # Variables for start and end times of each meeting
    # We'll use Real variables for flexibility
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
    s.add(robert_meet_start >= 0)  # Since we start at 9:00 AM (0 mins)
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

    # We need to model the order in which we visit friends and the travel times between them.
    # This is complex, so we'll assume a specific order and check feasibility.
    # Alternatively, we can use a more sophisticated approach with additional variables for order.

    # For simplicity, let's assume the order is Robert -> Rebecca -> Andrew -> Sarah -> Nancy.
    # This is a heuristic; a more complete solution would explore all possible orders.

    # Start at Union Square at time 0.
    # First, travel to Robert's location (The Castro): travel time 19 mins.
    s.add(robert_meet_start >= 19)
    # After meeting Robert, travel to next friend.
    # Next is Rebecca in Chinatown. Travel time from The Castro to Chinatown is 20 mins.
    s.add(rebecca_meet_start >= robert_meet_end + 20)
    # After Rebecca, travel to Andrew in Golden Gate Park. Travel time from Chinatown to Golden Gate Park is 23 mins.
    s.add(andrew_meet_start >= rebecca_meet_end + 23)
    # After Andrew, travel to Sarah in Pacific Heights. Travel time from Golden Gate Park to Pacific Heights is 16 mins.
    s.add(sarah_meet_start >= andrew_meet_end + 16)
    # After Sarah, travel to Nancy in Presidio. Travel time from Pacific Heights to Presidio is 11 mins.
    s.add(nancy_meet_start >= sarah_meet_end + 11)

    # Check if this order is feasible
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found:")
        print(f"Meet Robert at The Castro: from {m[robert_meet_start]} to {m[robert_meet_end]}")
        print(f"Meet Rebecca at Chinatown: from {m[rebecca_meet_start]} to {m[rebecca_meet_end]}")
        print(f"Meet Andrew at Golden Gate Park: from {m[andrew_meet_start]} to {m[andrew_meet_end]}")
        print(f"Meet Sarah at Pacific Heights: from {m[sarah_meet_start]} to {m[sarah_meet_end]}")
        print(f"Meet Nancy at Presidio: from {m[nancy_meet_start]} to {m[nancy_meet_end]}")
    else:
        print("No feasible schedule found with the assumed order.")

    # Alternatively, to maximize the number of friends met, we can use a more flexible approach.
    # However, that would require more complex modeling, such as using indicator variables for whether each friend is met.

solve_scheduling()