from z3 import *

def solve_scheduling_problem():
    # Initialize solver
    solver = Solver()

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
        solver.add(var['start'] >= data['start'])
        solver.add(var['end'] <= data['end'])
        solver.add(var['end'] == var['start'] + data['duration'])
        # The meeting must happen if met is True
        solver.add(Implies(var['met'], And(var['start'] >= current_time, var['end'] <= data['end'])))

    # Let's try to meet Timothy first, then Patricia, then Ashley.
    # This is a heuristic; a more general solution would involve sequencing variables.

    # Timothy's meeting
    t_start = meet_vars['Timothy']['start']
    t_end = meet_vars['Timothy']['end']
    solver.add(Implies(meet_vars['Timothy']['met'], t_start >= current_time + travel_times[(current_location, 'Embarcadero')]))
    solver.add(Implies(meet_vars['Timothy']['met'], t_end <= friends['Timothy']['end']))

    # After Timothy, travel to Patricia's location (Nob Hill)
    next_time_after_t = t_end + travel_times[('Embarcadero', 'Nob Hill')]
    p_start = meet_vars['Patricia']['start']
    p_end = meet_vars['Patricia']['end']
    solver.add(Implies(And(meet_vars['Timothy']['met'], meet_vars['Patricia']['met']), p_start >= next_time_after_t))

    # After Patricia, travel to Ashley's location (Mission District)
    next_time_after_p = p_end + travel_times[('Nob Hill', 'Mission District')]
    a_start = meet_vars['Ashley']['start']
    a_end = meet_vars['Ashley']['end']
    solver.add(Implies(And(meet_vars['Patricia']['met'], meet_vars['Ashley']['met']), a_start >= next_time_after_p))

    # Maximize the number of friends met
    solver.maximize(
        Sum([
            If(meet_vars['Timothy']['met'], 1, 0),
            If(meet_vars['Patricia']['met'], 1, 0),
            If(meet_vars['Ashley']['met'], 1, 0)
        ])
    )

    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
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

# Run the solver and print the result
result = solve_scheduling_problem()
print(result)