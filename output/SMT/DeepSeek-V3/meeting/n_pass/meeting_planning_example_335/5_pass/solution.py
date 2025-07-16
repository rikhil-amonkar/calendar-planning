from z3 import *

def solve_scheduling():
    # Initialize solver with optimization capabilities
    s = Optimize()

    # Define friends and their availability
    friends = {
        'Helen': {'location': 'North Beach', 'start': 9*60, 'end': 17*60, 'duration': 15},
        'Betty': {'location': 'Financial District', 'start': 19*60, 'end': 21*60 + 45, 'duration': 90},
        'Amanda': {'location': 'Alamo Square', 'start': 19*60 + 45, 'end': 21*60, 'duration': 60},
        'Kevin': {'location': 'Mission District', 'start': 10*60 + 45, 'end': 14*60 + 45, 'duration': 45}
    }

    # Travel times between locations (in minutes)
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

    # Create variables for meeting times
    meeting_start = {name: Int(f'start_{name}') for name in friends}
    meeting_end = {name: Int(f'end_{name}') for name in friends}
    meet_friend = {name: Bool(f'meet_{name}') for name in friends}

    # Starting point
    current_location = 'Pacific Heights'
    current_time = 9 * 60  # 9:00 AM

    # Basic constraints for each friend
    for name in friends:
        friend = friends[name]
        s.add(Implies(meet_friend[name], 
              And(meeting_start[name] >= friend['start'],
                  meeting_end[name] <= friend['end'],
                  meeting_end[name] == meeting_start[name] + friend['duration'])))
        
        s.add(Implies(Not(meet_friend[name]), 
              And(meeting_start[name] == 0, 
                  meeting_end[name] == 0)))

    # Meeting sequence constraints
    # Kevin must be first if meeting him
    s.add(Implies(meet_friend['Kevin'], 
          meeting_start['Kevin'] >= current_time + travel_times[current_location]['Mission District']))

    # Helen can be after Kevin
    s.add(Implies(And(meet_friend['Kevin'], meet_friend['Helen']),
          meeting_start['Helen'] >= meeting_end['Kevin'] + travel_times['Mission District']['North Beach']))

    # Betty can be after Helen
    s.add(Implies(And(meet_friend['Helen'], meet_friend['Betty']),
          meeting_start['Betty'] >= meeting_end['Helen'] + travel_times['North Beach']['Financial District']))

    # Amanda can be after Helen
    s.add(Implies(And(meet_friend['Helen'], meet_friend['Amanda']),
          meeting_start['Amanda'] >= meeting_end['Helen'] + travel_times['North Beach']['Alamo Square']))

    # Cannot meet both Betty and Amanda
    s.add(Or(Not(meet_friend['Betty']), Not(meet_friend['Amanda'])))

    # Maximize number of friends met
    s.maximize(Sum([If(meet_friend[name], 1, 0) for name in friends]))

    # Solve and display results
    if s.check() == sat:
        m = s.model()
        met_friends = [name for name in friends if m.evaluate(meet_friend[name])]
        print(f"Optimal schedule meets {len(met_friends)} friends:")
        
        for name in sorted(met_friends, key=lambda x: m.evaluate(meeting_start[x]).as_long()):
            start = m.evaluate(meeting_start[name]).as_long()
            end = m.evaluate(meeting_end[name]).as_long()
            print(f"Meet {name} at {friends[name]['location']} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
    else:
        print("No feasible schedule found")

solve_scheduling()