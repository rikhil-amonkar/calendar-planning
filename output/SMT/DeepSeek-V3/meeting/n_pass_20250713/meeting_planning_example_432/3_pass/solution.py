from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define locations and friends
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
        # If meeting the friend, constrain the time
        s.add(Implies(meet_friend[name], meeting_start[name] >= friend['available_start']))
        s.add(Implies(meet_friend[name], meeting_end[name] <= friend['available_end']))
        s.add(Implies(meet_friend[name], meeting_end[name] == meeting_start[name] + friend['duration']))

    # Exactly 4 friends must be met
    s.add(Sum([If(meet_friend[name], 1, 0) for name in friends]) == 4)

    # Define possible meeting orders (we'll try one possible order)
    # Order: David -> Barbara -> Kevin -> Joseph
    ordered_friends = ['David', 'Barbara', 'Kevin', 'Joseph']

    # Initialize variables for tracking time and location
    prev_time = current_time
    prev_location = current_location

    # Add constraints for the selected meeting order
    for i, name in enumerate(ordered_friends):
        # Only add travel time if this isn't the first meeting
        if i > 0:
            travel_time = travel_times[(prev_location, friends[name]['location'])]
            s.add(Implies(meet_friend[name], meeting_start[name] >= prev_time + travel_time))
        else:
            s.add(Implies(meet_friend[name], meeting_start[name] >= prev_time + travel_times[(current_location, friends[name]['location'])]))

        # Update previous time and location
        prev_time = If(meet_friend[name], meeting_end[name], prev_time)
        prev_location = If(meet_friend[name], friends[name]['location'], prev_location)

    # Ensure we meet all friends in our selected order
    for name in ordered_friends:
        s.add(meet_friend[name])

    # Check if a valid schedule exists
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        for name in friends:
            if is_true(m[meet_friend[name]]):
                start = m[meeting_start[name]].as_long()
                end = m[meeting_end[name]].as_long()
                print(f"Meet {name} at {friends[name]['location']} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
    else:
        print("No valid schedule found with this meeting order. Try a different order.")

solve_scheduling()