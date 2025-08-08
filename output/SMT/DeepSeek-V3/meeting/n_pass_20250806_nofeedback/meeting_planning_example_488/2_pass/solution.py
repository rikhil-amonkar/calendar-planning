from z3 import *

def solve_scheduling_problem():
    s = Optimize()  # Using Optimize for maximize functionality

    # Locations and their indices
    locations = {
        'Pacific Heights': 0,
        'Nob Hill': 1,
        'Russian Hill': 2,
        'The Castro': 3,
        'Sunset District': 4,
        'Haight-Ashbury': 5
    }

    # Travel times between locations (in minutes)
    travel_times = [
        [0, 8, 7, 16, 21, 11],    # Pacific Heights
        [8, 0, 5, 17, 25, 13],     # Nob Hill
        [7, 5, 0, 21, 23, 17],     # Russian Hill
        [16, 16, 18, 0, 17, 6],    # The Castro
        [21, 27, 24, 17, 0, 15],   # Sunset District
        [12, 15, 17, 6, 15, 0]     # Haight-Ashbury
    ]

    # Friends data (all times in minutes since midnight)
    friends = [
        {'name': 'Ronald', 'location': 'Nob Hill', 'start': 600, 'end': 1020, 'min_duration': 105},
        {'name': 'Sarah', 'location': 'Russian Hill', 'start': 435, 'end': 570, 'min_duration': 45},
        {'name': 'Helen', 'location': 'The Castro', 'start': 810, 'end': 1020, 'min_duration': 120},
        {'name': 'Joshua', 'location': 'Sunset District', 'start': 855, 'end': 1170, 'min_duration': 90},
        {'name': 'Margaret', 'location': 'Haight-Ashbury', 'start': 615, 'end': 1320, 'min_duration': 60}
    ]

    # Initialize variables
    current_time = Int('initial_time')
    s.add(current_time == 540)  # Start at 9:00 AM (540 minutes)
    current_location = Int('initial_loc')
    s.add(current_location == locations['Pacific Heights'])

    # Create variables for each meeting
    meets = []
    itinerary_vars = []

    for i, friend in enumerate(friends):
        # Decision variable: whether to meet this friend
        meet = Bool(f"meet_{friend['name']}")
        meets.append(meet)

        # Meeting start and end times
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")

        # Travel time to this friend's location
        travel_time = Int(f"travel_{friend['name']}")
        loc_index = locations[friend['location']]
        
        # Create a travel time expression that depends on current_location
        travel_expr = 0
        for j in range(len(travel_times)):
            travel_expr = If(current_location == j, travel_times[j][loc_index], travel_expr)
        s.add(travel_time == travel_expr)

        # Constraints if we meet this friend
        s.add(Implies(meet, start >= friend['start']))
        s.add(Implies(meet, end <= friend['end']))
        s.add(Implies(meet, end - start >= friend['min_duration']))
        s.add(Implies(meet, start >= current_time + travel_time))

        # Update current time and location if we meet this friend
        new_time = If(meet, end, current_time)
        new_location = If(meet, loc_index, current_location)
        
        itinerary_vars.append({
            'name': friend['name'],
            'meet': meet,
            'start': start,
            'end': end,
            'new_time': new_time,
            'new_location': new_location
        })

        current_time = new_time
        current_location = new_location

    # Maximize the number of friends met
    s.maximize(Sum([If(meet, 1, 0) for meet in meets]))

    if s.check() == sat:
        model = s.model()
        result = []
        for entry in itinerary_vars:
            if is_true(model[entry['meet']]):
                start_val = model[entry['start']].as_long()
                end_val = model[entry['end']].as_long()
                start_str = f"{start_val // 60:02d}:{start_val % 60:02d}"
                end_str = f"{end_val // 60:02d}:{end_val % 60:02d}"
                result.append({
                    "action": "meet",
                    "person": entry['name'],
                    "start_time": start_str,
                    "end_time": end_str
                })
        return {"itinerary": result}
    else:
        return {"itinerary": []}

solution = solve_scheduling_problem()
print(solution)