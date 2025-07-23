from z3 import *

def solve_scheduling_problem():
    # Initialize optimizer
    opt = Optimize()

    # Define time in minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Travel times dictionary: (from, to) -> minutes
    travel_times = {
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'Mission District'): 13,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Mission District', 'Russian Hill'): 15,
        ('Mission District', 'Nob Hill'): 12,
        ('Mission District', 'Embarcadero'): 19,
        ('Embarcadero', 'Russian Hill'): 8,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Mission District'): 20,
    }

    # Friends' availability
    friends = {
        'Patricia': {
            'location': 'Nob Hill',
            'start': time_to_minutes('18:30'),  # 6:30 PM
            'end': time_to_minutes('21:45'),     # 9:45 PM
            'duration': 90
        },
        'Ashley': {
            'location': 'Mission District',
            'start': time_to_minutes('20:30'),   # 8:30 PM
            'end': time_to_minutes('21:15'),     # 9:15 PM
            'duration': 45
        },
        'Timothy': {
            'location': 'Embarcadero',
            'start': time_to_minutes('09:45'),   # 9:45 AM
            'end': time_to_minutes('17:45'),     # 5:45 PM
            'duration': 120
        }
    }

    # Variables for each meeting: start and end times in minutes since 9:00 AM (540)
    meet_vars = {}
    for name in friends:
        meet_vars[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'met': Bool(f'met_{name}')
        }

    # Current location starts at Russian Hill at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Russian Hill'

    # Constraints for each friend
    for name in friends:
        data = friends[name]
        var = meet_vars[name]
        opt.add(Implies(var['met'], And(
            var['start'] >= data['start'],
            var['end'] <= data['end'],
            var['end'] == var['start'] + data['duration']
        )))

    # Sequence constraints: ensure meetings are scheduled in some order with travel times
    # We'll create a variable for the order of meetings
    order = {name: Int(f'order_{name}') for name in friends}
    for name in friends:
        opt.add(Implies(meet_vars[name]['met'], And(order[name] >= 0, order[name] <= 2)))

    # All met meetings have distinct order values
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                opt.add(Implies(And(meet_vars[name1]['met'], meet_vars[name2]['met']), order[name1] != order[name2]))

    # Determine the sequence and apply travel times
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                # If name1 is before name2 in order, then name2's start >= name1's end + travel time
                travel_time = travel_times[(friends[name1]['location'], friends[name2]['location'])]
                opt.add(Implies(
                    And(
                        meet_vars[name1]['met'],
                        meet_vars[name2]['met'],
                        order[name1] < order[name2]
                    ),
                    meet_vars[name2]['start'] >= meet_vars[name1]['end'] + travel_time
                ))

    # The first meeting must start after current_time + travel time from Russian Hill
    for name in friends:
        travel_time = travel_times[(current_location, friends[name]['location'])]
        opt.add(Implies(
            And(
                meet_vars[name]['met'],
                order[name] == 0
            ),
            meet_vars[name]['start'] >= current_time + travel_time
        ))

    # Maximize the number of friends met
    opt.maximize(
        Sum([
            If(meet_vars['Timothy']['met'], 1, 0),
            If(meet_vars['Patricia']['met'], 1, 0),
            If(meet_vars['Ashley']['met'], 1, 0)
        ])
    )

    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for name in friends:
            if is_true(model.eval(meet_vars[name]['met'])):
                start = model.eval(meet_vars[name]['start']).as_long()
                end = model.eval(meet_vars[name]['end']).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x['start_time']))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the optimizer and print the result
result = solve_scheduling_problem()
print(result)