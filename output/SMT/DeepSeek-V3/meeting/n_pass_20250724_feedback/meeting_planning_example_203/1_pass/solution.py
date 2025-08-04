from z3 import *
import json

def solve_scheduling_problem():
    # Initialize the solver
    s = Solver()

    # Define the travel times between locations (in minutes)
    travel_times = {
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'Mission District'): 17,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Pacific Heights', 'Financial District'): 13,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Pacific Heights', 'Mission District'): 15,
        ('Mission District', 'Financial District'): 17,
        ('Mission District', 'Fisherman\'s Wharf'): 22,
        ('Mission District', 'Pacific Heights'): 16
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Friends' availability and constraints
    friends = {
        'David': {
            'location': 'Fisherman\'s Wharf',
            'start': time_to_minutes('10:45'),
            'end': time_to_minutes('15:30'),
            'min_duration': 15
        },
        'Timothy': {
            'location': 'Pacific Heights',
            'start': time_to_minutes('9:00'),
            'end': time_to_minutes('15:30'),
            'min_duration': 75
        },
        'Robert': {
            'location': 'Mission District',
            'start': time_to_minutes('12:15'),
            'end': time_to_minutes('19:45'),
            'min_duration': 90
        }
    }

    # Current location starts at Financial District at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Financial District'

    # Variables for each meeting's start and end times
    meet_vars = {}
    for name in friends:
        meet_vars[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'met': Bool(f'met_{name}')
        }

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        var = meet_vars[name]
        s.add(Implies(var['met'], var['start'] >= friend['start']))
        s.add(Implies(var['met'], var['end'] <= friend['end']))
        s.add(Implies(var['met'], var['end'] == var['start'] + friend['min_duration']))

    # Constraints for meeting order and travel times
    # We need to decide the order in which to meet friends, but since there are three, we'll consider all permutations.
    # However, with Z3, we can model the order as a permutation and add constraints accordingly.
    # Alternatively, we can assume a specific order and check feasibility, but that's not general.
    # Here, we'll model the possibility of meeting each friend in some order, with travel times between.

    # We'll create a list of possible meeting sequences and check which one fits.
    # But for three friends, there are 3! = 6 possible orders.
    # We'll generate all possible orders and let Z3 choose the feasible one.

    # Let's create a list of all possible meeting orders (permutations of the three friends)
    from itertools import permutations
    possible_orders = list(permutations(['David', 'Timothy', 'Robert']))

    # We'll create a variable to represent which order is chosen
    order_choice = Int('order_choice')
    s.add(order_choice >= 0, order_choice < len(possible_orders))

    # Now, for each possible order, we'll add constraints that if this order is chosen, the meetings must follow the sequence with travel times.
    # We'll use the order_choice to index into possible_orders.

    # Create variables for the start and end times of the entire schedule
    # We'll need to track the current time after each meeting and travel.

    # We'll model the schedule step by step based on the chosen order.
    # For each position in the order, we'll have constraints on the start time based on the previous action.

    # Let's create variables for the start time of each meeting in the sequence.
    # The first meeting's start time is >= current_time + travel time from current_location to the friend's location.
    # Then, the next meeting's start time is >= previous meeting's end time + travel time.

    # To model this, we'll create variables for the start and end times of each step in the sequence.

    # Create variables for the steps in the sequence.
    step_start = [Int(f'step_{i}_start') for i in range(3)]
    step_end = [Int(f'step_{i}_end') for i in range(3)]
    step_person = [Int(f'step_{i}_person') for i in range(3)]  # 0: David, 1: Timothy, 2: Robert

    # For each possible order, we'll add constraints that if order_choice is i, then step_person follows possible_orders[i].
    for i, order in enumerate(possible_orders):
        for step in range(3):
            s.add(Implies(order_choice == i, step_person[step] == ['David', 'Timothy', 'Robert'].index(order[step])))

    # Now, constraints for the first step.
    # The first step's start time is current_time + travel from current_location to the first friend's location.
    for i, order in enumerate(possible_orders):
        first_person = order[0]
        first_location = friends[first_person]['location']
        travel_time = travel_times[(current_location, first_location)]
        s.add(Implies(order_choice == i, step_start[0] == current_time + travel_time))
        s.add(Implies(order_choice == i, step_end[0] == step_start[0] + friends[first_person]['min_duration']))
        # The meeting must be within the friend's availability.
        s.add(Implies(order_choice == i, meet_vars[first_person]['start'] == step_start[0]))
        s.add(Implies(order_choice == i, meet_vars[first_person]['end'] == step_end[0]))
        s.add(Implies(order_choice == i, meet_vars[first_person]['met']))

    # Constraints for the second step.
    for i, order in enumerate(possible_orders):
        if len(order) < 2:
            continue
        first_person = order[0]
        second_person = order[1]
        first_location = friends[first_person]['location']
        second_location = friends[second_person]['location']
        travel_time = travel_times[(first_location, second_location)]
        s.add(Implies(order_choice == i, step_start[1] >= step_end[0] + travel_time))
        s.add(Implies(order_choice == i, step_end[1] == step_start[1] + friends[second_person]['min_duration']))
        s.add(Implies(order_choice == i, meet_vars[second_person]['start'] == step_start[1]))
        s.add(Implies(order_choice == i, meet_vars[second_person]['end'] == step_end[1]))
        s.add(Implies(order_choice == i, meet_vars[second_person]['met']))

    # Constraints for the third step.
    for i, order in enumerate(possible_orders):
        if len(order) < 3:
            continue
        second_person = order[1]
        third_person = order[2]
        second_location = friends[second_person]['location']
        third_location = friends[third_person]['location']
        travel_time = travel_times[(second_location, third_location)]
        s.add(Implies(order_choice == i, step_start[2] >= step_end[1] + travel_time))
        s.add(Implies(order_choice == i, step_end[2] == step_start[2] + friends[third_person]['min_duration']))
        s.add(Implies(order_choice == i, meet_vars[third_person]['start'] == step_start[2]))
        s.add(Implies(order_choice == i, meet_vars[third_person]['end'] == step_end[2]))
        s.add(Implies(order_choice == i, meet_vars[third_person]['met']))

    # Ensure all meetings are within their availability windows.
    for name in friends:
        friend = friends[name]
        var = meet_vars[name]
        s.add(Implies(var['met'], var['start'] >= friend['start']))
        s.add(Implies(var['met'], var['end'] <= friend['end']))

    # Maximize the number of friends met (or total meeting time)
    # Here, we prioritize meeting all three friends.
    s.add(And([meet_vars[name]['met'] for name in friends]))

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
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
        # Sort the itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x['start_time']))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the solver
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))