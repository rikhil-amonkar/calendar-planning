from z3 import *
import json

def main():
    # Define friends and their details
    friends = ['Rebecca', 'Linda', 'Elizabeth', 'William', 'Robert', 'Mark']
    locations = {
        'Rebecca': 'Presidio',
        'Linda': 'Sunset District',
        'Elizabeth': 'Haight-Ashbury',
        'William': 'Mission District',
        'Robert': 'Golden Gate Park',
        'Mark': 'Russian Hill'
    }
    available_start = {
        'Rebecca': 18*60 + 15,  # 6:15 PM
        'Linda': 15*60 + 30,     # 3:30 PM
        'Elizabeth': 17*60 + 15, # 5:15 PM
        'William': 13*60 + 15,   # 1:15 PM
        'Robert': 14*60 + 15,    # 2:15 PM
        'Mark': 10*60            # 10:00 AM
    }
    available_end = {
        'Rebecca': 20*60 + 45,  # 8:45 PM
        'Linda': 19*60 + 45,     # 7:45 PM
        'Elizabeth': 19*60 + 30, # 7:30 PM
        'William': 19*60 + 30,   # 7:30 PM
        'Robert': 21*60 + 30,    # 9:30 PM
        'Mark': 21*60 + 15       # 9:15 PM
    }
    min_duration = {
        'Rebecca': 60,
        'Linda': 30,
        'Elizabeth': 105,
        'William': 30,
        'Robert': 45,
        'Mark': 75
    }

    # Travel times dictionary
    travel_dict = {
        ('The Castro', 'Presidio'): 20,
        ('The Castro', 'Sunset District'): 17,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('The Castro', 'Mission District'): 7,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Russian Hill'): 18,
        ('Presidio', 'The Castro'): 21,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Mission District'): 26,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Russian Hill'): 14,
        ('Sunset District', 'The Castro'): 17,
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Mission District'): 24,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Russian Hill'): 24,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Mission District', 'The Castro'): 7,
        ('Mission District', 'Presidio'): 25,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Russian Hill'): 15,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Golden Gate Park'): 21
    }

    # Create Z3 variables
    meet_vars = {name: Bool(f'meet_{name}') for name in friends}
    start_vars = {name: Real(f'start_{name}') for name in friends}

    # Initialize solver and optimizer
    opt = Optimize()

    # Constraint: Meeting must be within the friend's availability window
    for name in friends:
        opt.add(Implies(meet_vars[name], start_vars[name] >= available_start[name]))
        opt.add(Implies(meet_vars[name], start_vars[name] + min_duration[name] <= available_end[name]))

    # Constraint: Travel time from The Castro to the first meeting
    for name in friends:
        loc = locations[name]
        travel_time = travel_dict[('The Castro', loc)]
        opt.add(Implies(meet_vars[name], start_vars[name] >= 9*60 + travel_time))

    # Constraint: Travel time between consecutive meetings
    for i in friends:
        for j in friends:
            if i == j:
                continue
            loc_i = locations[i]
            loc_j = locations[j]
            travel_ij = travel_dict[(loc_i, loc_j)]
            travel_ji = travel_dict[(loc_j, loc_i)]
            constraint = Or(
                start_vars[i] + min_duration[i] + travel_ij <= start_vars[j],
                start_vars[j] + min_duration[j] + travel_ji <= start_vars[i]
            )
            opt.add(Implies(And(meet_vars[i], meet_vars[j]), constraint))

    # Objective: Maximize the number of friends met
    opt.maximize(Sum([If(meet_vars[name], 1, 0) for name in friends]))

    # Solve the model
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for name in friends:
            if model.eval(meet_vars[name]):
                start_val = model.eval(start_vars[name])
                if is_rational_value(start_val):
                    num = start_val.numerator_as_long()
                    den = start_val.denominator_as_long()
                    start_minutes = num // den
                else:
                    start_minutes = start_val.as_long()
                end_minutes = start_minutes + min_duration[name]
                start_time = f"{start_minutes // 60:02d}:{start_minutes % 60:02d}"
                end_time = f"{end_minutes // 60:02d}:{end_minutes % 60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time
                })
        itinerary.sort(key=lambda x: x['start_time'])
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()