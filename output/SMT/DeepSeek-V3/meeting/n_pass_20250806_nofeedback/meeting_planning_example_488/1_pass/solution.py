from z3 import *

def solve_scheduling_problem():
    s = Solver()

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

    # Friends data
    friends = [
        {'name': 'Ronald', 'location': 'Nob Hill', 'start': 600, 'end': 1020, 'min_duration': 105},
        {'name': 'Sarah', 'location': 'Russian Hill', 'start': 435, 'end': 570, 'min_duration': 45},
        {'name': 'Helen', 'location': 'The Castro', 'start': 810, 'end': 1020, 'min_duration': 120},
        {'name': 'Joshua', 'location': 'Sunset District', 'start': 855, 'end': 1170, 'min_duration': 90},
        {'name': 'Margaret', 'location': 'Haight-Ashbury', 'start': 615, 'end': 1320, 'min_duration': 60}
    ]

    # Current time starts at 9:00 AM (540 minutes)
    current_time = 540
    current_location = locations['Pacific Heights']
    itinerary = []

    # Variables to track if we meet each friend
    meet_friends = [Bool(f"meet_{friend['name']}") for friend in friends]

    for i, friend in enumerate(friends):
        loc = locations[friend['location']]
        travel_time = travel_times[current_location][loc]

        # Variables for start and end times
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        duration = end - start

        # Constraints if we meet the friend
        s.add(Implies(meet_friends[i], start >= friend['start']))
        s.add(Implies(meet_friends[i], end <= friend['end']))
        s.add(Implies(meet_friends[i], duration >= friend['min_duration']))
        s.add(Implies(meet_friends[i], start >= current_time + travel_time))

        # Update current time and location if we meet the friend
        new_time = If(meet_friends[i], end, current_time)
        new_location = If(meet_friends[i], loc, current_location)
        current_time = new_time
        current_location = new_location

        # Add to itinerary if meeting
        itinerary.append({
            'name': friend['name'],
            'start': start,
            'end': end,
            'meet': meet_friends[i]
        })

    # Maximize the number of friends met
    s.maximize(Sum([If(meet, 1, 0) for meet in meet_friends]))

    if s.check() == sat:
        model = s.model()
        result = []
        for entry in itinerary:
            if is_true(model[entry['meet']]):
                start_time = model[entry['start']].as_long()
                end_time = model[entry['end']].as_long()
                start_str = f"{start_time // 60:02d}:{start_time % 60:02d}"
                end_str = f"{end_time // 60:02d}:{end_time % 60:02d}"
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