from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define locations and friends
    locations = ['GoldenGatePark', 'FishermansWharf', 'Bayview', 'MissionDistrict', 'Embarcadero', 'FinancialDistrict']
    friends = {
        'Joseph': {'location': 'FishermansWharf', 'available_start': 8*60, 'available_end': 17.5*60, 'duration': 90},
        'Jeffrey': {'location': 'Bayview', 'available_start': 17.5*60, 'available_end': 21.5*60, 'duration': 60},
        'Kevin': {'location': 'MissionDistrict', 'available_start': 11.25*60, 'available_end': 15.25*60, 'duration': 30},
        'David': {'location': 'Embarcadero', 'available_start': 8.25*60, 'available_end': 9*60, 'duration': 30},
        'Barbara': {'location': 'FinancialDistrict', 'available_start': 10.5*60, 'available_end': 16.5*60, 'duration': 15}
    }

    # Travel times dictionary (in minutes)
    travel_times = {
        ('GoldenGatePark', 'FishermansWharf'): 24,
        ('GoldenGatePark', 'Bayview'): 23,
        ('GoldenGatePark', 'MissionDistrict'): 17,
        ('GoldenGatePark', 'Embarcadero'): 25,
        ('GoldenGatePark', 'FinancialDistrict'): 26,
        ('FishermansWharf', 'GoldenGatePark'): 25,
        ('FishermansWharf', 'Bayview'): 26,
        ('FishermansWharf', 'MissionDistrict'): 22,
        ('FishermansWharf', 'Embarcadero'): 8,
        ('FishermansWharf', 'FinancialDistrict'): 11,
        ('Bayview', 'GoldenGatePark'): 22,
        ('Bayview', 'FishermansWharf'): 25,
        ('Bayview', 'MissionDistrict'): 13,
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'FinancialDistrict'): 19,
        ('MissionDistrict', 'GoldenGatePark'): 17,
        ('MissionDistrict', 'FishermansWharf'): 22,
        ('MissionDistrict', 'Bayview'): 15,
        ('MissionDistrict', 'Embarcadero'): 19,
        ('MissionDistrict', 'FinancialDistrict'): 17,
        ('Embarcadero', 'GoldenGatePark'): 25,
        ('Embarcadero', 'FishermansWharf'): 6,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'MissionDistrict'): 20,
        ('Embarcadero', 'FinancialDistrict'): 5,
        ('FinancialDistrict', 'GoldenGatePark'): 23,
        ('FinancialDistrict', 'FishermansWharf'): 10,
        ('FinancialDistrict', 'Bayview'): 19,
        ('FinancialDistrict', 'MissionDistrict'): 17,
        ('FinancialDistrict', 'Embarcadero'): 4
    }

    # Variables for each friend's meeting start and end times
    meeting_start = {name: Int(f'start_{name}') for name in friends}
    meeting_end = {name: Int(f'end_{name}') for name in friends}

    # Binary variables to indicate if a friend is met
    meet_friend = {name: Bool(f'meet_{name}') for name in friends}

    # Current location starts at Golden Gate Park at 9:00 AM (540 minutes)
    current_time = 9 * 60
    current_location = 'GoldenGatePark'

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        loc = friend['location']
        # If meeting the friend, constrain the time
        s.add(Implies(meet_friend[name], meeting_start[name] >= friend['available_start']))
        s.add(Implies(meet_friend[name], meeting_end[name] <= friend['available_end']))
        s.add(Implies(meet_friend[name], meeting_end[name] == meeting_start[name] + friend['duration']))

    # Exactly 4 friends must be met
    s.add(Sum([If(meet_friend[name], 1, 0) for name in friends]) == 4)

    # Define the order of meetings
    # We'll try to meet David first (earliest availability), then Barbara, Kevin, and Joseph
    # This is a heuristic; adjust if no solution is found
    s.add(meet_friend['David'])
    s.add(meet_friend['Barbara'])
    s.add(meet_friend['Kevin'])
    s.add(meet_friend['Joseph'])

    # Constraints for travel times between meetings
    # Meet David at Embarcadero
    s.add(Implies(meet_friend['David'], meeting_start['David'] >= current_time + travel_times[(current_location, 'Embarcadero')]))
    # After meeting David, update current time and location
    next_time = If(meet_friend['David'], meeting_end['David'], current_time)
    next_location = If(meet_friend['David'], 'Embarcadero', current_location)

    # Meet Barbara at Financial District
    s.add(Implies(meet_friend['Barbara'], meeting_start['Barbara'] >= next_time + travel_times[(next_location, 'FinancialDistrict')]))
    next_time = If(meet_friend['Barbara'], meeting_end['Barbara'], next_time)
    next_location = If(meet_friend['Barbara'], 'FinancialDistrict', next_location)

    # Meet Kevin at Mission District
    s.add(Implies(meet_friend['Kevin'], meeting_start['Kevin'] >= next_time + travel_times[(next_location, 'MissionDistrict')]))
    next_time = If(meet_friend['Kevin'], meeting_end['Kevin'], next_time)
    next_location = If(meet_friend['Kevin'], 'MissionDistrict', next_location)

    # Meet Joseph at Fisherman's Wharf
    s.add(Implies(meet_friend['Joseph'], meeting_start['Joseph'] >= next_time + travel_times[(next_location, 'FishermansWharf')]))
    next_time = If(meet_friend['Joseph'], meeting_end['Joseph'], next_time)
    next_location = If(meet_friend['Joseph'], 'FishermansWharf', next_location)

    # Check if a valid schedule exists
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        for name in friends:
            if m[meet_friend[name]]:
                start = m[meeting_start[name]].as_long()
                end = m[meeting_end[name]].as_long()
                print(f"Meet {name} at {friends[name]['location']} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
    else:
        print("No valid schedule found.")

solve_scheduling()