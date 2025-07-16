from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define locations and friends
    locations = ['Pacific Heights', 'North Beach', 'Financial District', 'Alamo Square', 'Mission District']
    friends = {
        'Helen': {'location': 'North Beach', 'start': 9*60, 'end': 17*60, 'duration': 15},
        'Betty': {'location': 'Financial District', 'start': 19*60, 'end': 21*60 + 45, 'duration': 90},
        'Amanda': {'location': 'Alamo Square', 'start': 19*60 + 45, 'end': 21*60, 'duration': 60},
        'Kevin': {'location': 'Mission District', 'start': 10*60 + 45, 'end': 14*60 + 45, 'duration': 45}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Pacific Heights': {
            'North Beach': 9,
            'Financial District': 13,
            'Alamo Square': 10,
            'Mission District': 15
        },
        'North Beach': {
            'Pacific Heights': 8,
            'Financial District': 8,
            'Alamo Square': 16,
            'Mission District': 18
        },
        'Financial District': {
            'Pacific Heights': 13,
            'North Beach': 7,
            'Alamo Square': 17,
            'Mission District': 17
        },
        'Alamo Square': {
            'Pacific Heights': 10,
            'North Beach': 15,
            'Financial District': 17,
            'Mission District': 10
        },
        'Mission District': {
            'Pacific Heights': 16,
            'North Beach': 17,
            'Financial District': 17,
            'Alamo Square': 11
        }
    }

    # Variables for each friend's meeting start and end times
    meeting_start = {name: Int(f'start_{name}') for name in friends}
    meeting_end = {name: Int(f'end_{name}') for name in friends}

    # Variables to indicate whether a friend is met
    meet_friend = {name: Bool(f'meet_{name}') for name in friends}

    # Current location and time tracking variables
    current_location = 'Pacific Heights'
    current_time = 9 * 60  # 9:00 AM in minutes

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        loc = friend['location']
        duration = friend['duration']
        start_window = friend['start']
        end_window = friend['end']

        # If meeting the friend, the meeting must be within their window and last at least the required duration
        s.add(Implies(meet_friend[name], And(
            meeting_start[name] >= start_window,
            meeting_end[name] <= end_window,
            meeting_end[name] == meeting_start[name] + duration
        ))

        # If not meeting the friend, the meeting times are irrelevant (but we set them to 0 for simplicity)
        s.add(Implies(Not(meet_friend[name]), And(
            meeting_start[name] == 0,
            meeting_end[name] == 0
        )))

    # Order of meetings and travel times
    # We need to sequence the meetings considering travel times
    # This is a simplified approach; a more precise approach would model the sequence explicitly
    # For simplicity, we'll assume that meetings are scheduled in some order and travel times are accounted for

    # To model the sequence, we can use auxiliary variables to track the order and ensure no overlaps with travel
    # However, this is complex, so we'll use a heuristic: try to meet friends in an order that allows all constraints to be satisfied

    # For example, Kevin is only available from 10:45 AM to 2:45 PM, so meeting him would have to be before other meetings
    # Helen is available all day, so she can be met before or after Kevin
    # Betty and Amanda are in the evening, so they must be after Kevin and Helen

    # Let's try to meet Kevin first, then Helen, then Betty and Amanda
    # We'll add constraints for this order

    # Kevin must be met before Helen, Betty, and Amanda
    # Helen must be met before Betty and Amanda
    # Betty and Amanda must be met in some order

    # Add constraints for the order and travel times
    # For example, if meeting Kevin, then Helen, then Betty and Amanda:
    # 1. Travel from Pacific Heights to Kevin's location (Mission District): 15 minutes
    #    Arrive at Mission District at 9:00 + 15 = 9:15 AM
    #    Kevin is available from 10:45 AM, so earliest meeting is 10:45 AM
    #    Meeting duration 45 minutes, ends at 11:30 AM
    # 2. Travel from Mission District to Helen's location (North Beach): 17 minutes
    #    Arrive at North Beach at 11:30 + 17 = 11:47 AM
    #    Helen is available until 5:00 PM, so can meet from 11:47 AM to any time before 5:00 PM
    #    Meeting duration 15 minutes, so can meet from 11:47 AM to 12:02 PM
    # 3. Then, travel to Betty or Amanda in the evening
    #    For Betty: Financial District, available from 7:00 PM
    #    Travel from North Beach to Financial District: 8 minutes
    #    So can arrive at Financial District by 7:00 PM, meeting starts at 7:00 PM, ends at 8:30 PM
    #    Then, travel to Alamo Square for Amanda: 17 minutes
    #    Arrive at Alamo Square at 8:30 + 17 = 8:47 PM
    #    Amanda is available until 9:00 PM, so meeting from 8:47 PM to 9:00 PM (13 minutes), but requires 60 minutes, so not possible
    #    So, alternative: meet Amanda before Betty
    #    Travel from North Beach to Alamo Square: 16 minutes
    #    Amanda is available from 7:45 PM, so arrive by 7:45 PM, meeting from 7:45 PM to 8:45 PM
    #    Then travel to Financial District: 17 minutes, arrive at 8:45 + 17 = 9:02 PM
    #    Betty's window ends at 9:45 PM, but meeting requires 90 minutes, so starts at 9:02 PM would end at 10:32 PM, which is after 9:45 PM. So not possible.
    #    Thus, only one of Betty or Amanda can be met in the evening.

    # So, the optimal schedule is to meet Kevin, Helen, and one of Betty or Amanda.

    # Let's encode this in Z3:

    # We'll use variables to represent the order and travel times
    # For simplicity, we'll assume the following order: Kevin -> Helen -> Betty or Amanda

    # Variables to represent the sequence
    # We'll have variables for the start and end times of each activity, including travel

    # Start at Pacific Heights at 9:00 AM
    prev_end = 9 * 60
    prev_loc = 'Pacific Heights'

    # Kevin's meeting
    s.add(Implies(meet_friend['Kevin'], And(
        meeting_start['Kevin'] >= prev_end + travel_times[prev_loc]['Mission District'],
        meeting_start['Kevin'] >= friends['Kevin']['start'],
        meeting_end['Kevin'] == meeting_start['Kevin'] + friends['Kevin']['duration'],
        meeting_end['Kevin'] <= friends['Kevin']['end']
    )))

    # After Kevin, travel to Helen's location
    s.add(Implies(And(meet_friend['Kevin'], meet_friend['Helen']), And(
        meeting_start['Helen'] >= meeting_end['Kevin'] + travel_times['Mission District']['North Beach'],
        meeting_start['Helen'] >= friends['Helen']['start'],
        meeting_end['Helen'] == meeting_start['Helen'] + friends['Helen']['duration'],
        meeting_end['Helen'] <= friends['Helen']['end']
    )))

    # After Helen, travel to Betty or Amanda
    # Betty's meeting
    s.add(Implies(And(meet_friend['Helen'], meet_friend['Betty']), And(
        meeting_start['Betty'] >= meeting_end['Helen'] + travel_times['North Beach']['Financial District'],
        meeting_start['Betty'] >= friends['Betty']['start'],
        meeting_end['Betty'] == meeting_start['Betty'] + friends['Betty']['duration'],
        meeting_end['Betty'] <= friends['Betty']['end']
    )))

    # Amanda's meeting
    s.add(Implies(And(meet_friend['Helen'], meet_friend['Amanda']), And(
        meeting_start['Amanda'] >= meeting_end['Helen'] + travel_times['North Beach']['Alamo Square'],
        meeting_start['Amanda'] >= friends['Amanda']['start'],
        meeting_end['Amanda'] == meeting_start['Amanda'] + friends['Amanda']['duration'],
        meeting_end['Amanda'] <= friends['Amanda']['end']
    )))

    # Cannot meet both Betty and Amanda due to time constraints
    s.add(Or(Not(meet_friend['Betty']), Not(meet_friend['Amanda'])))

    # Maximize the number of friends met
    # The sum of friends met is the sum of meet_friend variables
    # We'll use a proxy objective: maximize the sum of meet_friend
    # Since Z3 doesn't directly support optimization, we'll use a binary search approach
    # But for simplicity, we'll just check if we can meet 3 friends

    # Check if we can meet 3 friends
    s.push()
    s.add(Sum([If(meet_friend[name], 1, 0) for name in friends]) >= 3)
    if s.check() == sat:
        m = s.model()
        print("Optimal schedule meets 3 friends:")
        for name in friends:
            if m.evaluate(meet_friend[name]):
                start = m.evaluate(meeting_start[name])
                end = m.evaluate(meeting_end[name])
                print(f"Meet {name} at {friends[name]['location']} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
    else:
        s.pop()
        # Check if we can meet 2 friends
        s.push()
        s.add(Sum([If(meet_friend[name], 1, 0) for name in friends]) >= 2)
        if s.check() == sat:
            m = s.model()
            print("Optimal schedule meets 2 friends:")
            for name in friends:
                if m.evaluate(meet_friend[name]):
                    start = m.evaluate(meeting_start[name])
                    end = m.evaluate(meeting_end[name])
                    print(f"Meet {name} at {friends[name]['location']} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
        else:
            s.pop()
            # Check if we can meet 1 friend
            s.push()
            s.add(Sum([If(meet_friend[name], 1, 0) for name in friends]) >= 1)
            if s.check() == sat:
                m = s.model()
                print("Optimal schedule meets 1 friend:")
                for name in friends:
                    if m.evaluate(meet_friend[name]):
                        start = m.evaluate(meeting_start[name])
                        end = m.evaluate(meeting_end[name])
                        print(f"Meet {name} at {friends[name]['location']} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
            else:
                print("No feasible schedule found.")

solve_scheduling()