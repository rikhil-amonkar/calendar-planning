from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Bayview': {
            'Embarcadero': 19,
            'Fisherman\'s Wharf': 25,
            'Financial District': 19
        },
        'Embarcadero': {
            'Bayview': 21,
            'Fisherman\'s Wharf': 6,
            'Financial District': 5
        },
        'Fisherman\'s Wharf': {
            'Bayview': 26,
            'Embarcadero': 8,
            'Financial District': 11
        },
        'Financial District': {
            'Bayview': 19,
            'Embarcadero': 4,
            'Fisherman\'s Wharf': 10
        }
    }

    # Friends' availability and constraints
    friends = {
        'Betty': {
            'location': 'Embarcadero',
            'start': (19, 45),  # 7:45 PM
            'end': (21, 45),      # 9:45 PM
            'duration': 15        # minutes
        },
        'Karen': {
            'location': 'Fisherman\'s Wharf',
            'start': (8, 45),     # 8:45 AM
            'end': (15, 0),       # 3:00 PM
            'duration': 30        # minutes
        },
        'Anthony': {
            'location': 'Financial District',
            'start': (9, 15),     # 9:15 AM
            'end': (21, 30),      # 9:30 PM
            'duration': 105       # minutes
        }
    }

    # Current location starts at Bayview at 9:00 AM (540 minutes since midnight)
    current_time = 9 * 60 + 0  # 9:00 AM in minutes
    current_location = 'Bayview'

    # Variables for each meeting's start and end times
    meet_vars = {}
    for name in friends:
        meet_vars[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}')
        }

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        start_time = friend['start'][0] * 60 + friend['start'][1]
        end_time = friend['end'][0] * 60 + friend['end'][1]
        duration = friend['duration']

        # Meeting must start within the friend's availability
        s.add(meet_vars[name]['start'] >= start_time)
        s.add(meet_vars[name]['end'] <= end_time)
        # Meeting duration
        s.add(meet_vars[name]['end'] == meet_vars[name]['start'] + duration)

    # Sequence constraints: order of meetings and travel times
    # We need to decide the order of meetings. Possible orders are permutations of the three friends.
    # We'll model this by allowing any order and adding constraints accordingly.

    # We'll create a variable for the order (0, 1, 2) for each friend.
    order = {name: Int(f'order_{name}') for name in friends}
    # Each order is unique and between 0 and 2
    s.add(Distinct([order[name] for name in friends]))
    for name in friends:
        s.add(order[name] >= 0, order[name] < 3)

    # For each possible pair of friends, if one comes before the other, add travel time constraints.
    names = list(friends.keys())
    for i in range(len(names)):
        for j in range(len(names)):
            if i == j:
                continue
            name1 = names[i]
            name2 = names[j]
            # If name1 comes before name2 in the order
            cond = order[name1] < order[name2]
            # Then name2's start time >= name1's end time + travel time from name1's location to name2's location
            loc1 = friends[name1]['location']
            loc2 = friends[name2]['location']
            travel = travel_times[loc1][loc2]
            s.add(Implies(cond, meet_vars[name2]['start'] >= meet_vars[name1]['end'] + travel))

    # The first meeting must start after current_time + travel from current_location to first meeting's location.
    for name in friends:
        loc = friends[name]['location']
        travel = travel_times[current_location][loc]
        s.add(Implies(order[name] == 0, meet_vars[name]['start'] >= current_time + travel))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        # Extract the meeting times
        itinerary = []
        # Determine the order of meetings
        meeting_order = sorted(friends.keys(), key=lambda x: m.evaluate(order[x]).as_long())
        for name in meeting_order:
            start = m.evaluate(meet_vars[name]['start']).as_long()
            end = m.evaluate(meet_vars[name]['end']).as_long()
            start_h = start // 60
            start_m = start % 60
            end_h = end // 60
            end_m = end % 60
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_h:02d}:{start_m:02d}",
                "end_time": f"{end_h:02d}:{end_m:02d}"
            })
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

result = solve_scheduling()
print(json.dumps(result, indent=2))