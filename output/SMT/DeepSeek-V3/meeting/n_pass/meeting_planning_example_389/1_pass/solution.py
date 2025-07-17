from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Haight-Ashbury': {
            'Fisherman\'s Wharf': 23,
            'Richmond District': 10,
            'Mission District': 11,
            'Bayview': 18
        },
        'Fisherman\'s Wharf': {
            'Haight-Ashbury': 22,
            'Richmond District': 18,
            'Mission District': 22,
            'Bayview': 26
        },
        'Richmond District': {
            'Haight-Ashbury': 10,
            'Fisherman\'s Wharf': 18,
            'Mission District': 20,
            'Bayview': 26
        },
        'Mission District': {
            'Haight-Ashbury': 12,
            'Fisherman\'s Wharf': 22,
            'Richmond District': 20,
            'Bayview': 15
        },
        'Bayview': {
            'Haight-Ashbury': 19,
            'Fisherman\'s Wharf': 25,
            'Richmond District': 25,
            'Mission District': 13
        }
    }

    # Friends' availability and constraints
    friends = {
        'Sarah': {
            'location': 'Fisherman\'s Wharf',
            'start': (14, 45),  # 2:45 PM
            'end': (17, 30),    # 5:30 PM
            'duration': 105    # minutes
        },
        'Mary': {
            'location': 'Richmond District',
            'start': (13, 0),   # 1:00 PM
            'end': (19, 15),    # 7:15 PM
            'duration': 75
        },
        'Helen': {
            'location': 'Mission District',
            'start': (21, 45),  # 9:45 PM
            'end': (22, 30),    # 10:30 PM
            'duration': 30
        },
        'Thomas': {
            'location': 'Bayview',
            'start': (15, 15),  # 3:15 PM
            'end': (18, 45),    # 6:45 PM
            'duration': 120
        }
    }

    # Current location and start time
    current_location = 'Haight-Ashbury'
    current_time = (9, 0)  # 9:00 AM

    # Convert all times to minutes since midnight for easier arithmetic
    def time_to_minutes(h, m):
        return h * 60 + m

    # Convert minutes back to (h, m)
    def minutes_to_time(t):
        return (t // 60, t % 60)

    # Initialize variables for each meeting's start and end times
    meeting_vars = {}
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        meeting_vars[name] = {
            'start': start_var,
            'end': end_var,
            'location': friends[name]['location'],
            'duration': friends[name]['duration'],
            'window_start': time_to_minutes(*friends[name]['start']),
            'window_end': time_to_minutes(*friends[name]['end'])
        }
        # Constrain meeting within friend's window
        s.add(start_var >= meeting_vars[name]['window_start'])
        s.add(end_var <= meeting_vars[name]['window_end'])
        s.add(end_var == start_var + meeting_vars[name]['duration'])

    # Variables to track order of meetings (using a list of possible orders)
    # Since there are 4 friends, there are 4! = 24 possible orders. We'll let Z3 find a feasible order.
    # To model the order, we'll use a list of booleans indicating whether one meeting is before another.
    # Alternatively, we can use a permutation approach, but it's complex. Instead, we'll use auxiliary variables to sequence meetings.

    # We'll create variables for the order: for each pair of meetings, decide which comes first.
    # But this is O(n^2). Instead, we'll use a more straightforward approach by creating a sequence.

    # We'll model the sequence as a list of meetings in some order, with constraints on travel times between them.
    # However, Z3 doesn't directly support lists, so we'll have to model the sequence with variables.

    # Alternative approach: assume a fixed order and check feasibility. If not, try another order.
    # But with Z3, we can encode the order as part of the constraints.

    # Let's create variables for the order indices.
    order = [Int(f'order_{i}') for i in range(4)]
    s.add(Distinct(order))
    s.add(And([order[i] >= 0 for i in range(4)]))
    s.add(And([order[i] < 4 for i in range(4)]))

    # Map order indices to friends
    friend_names = list(friends.keys())

    # Variables to track the start and end times of each meeting in the sequence
    seq_start = [Int(f'seq_start_{i}') for i in range(4)]
    seq_end = [Int(f'seq_end_{i}') for i in range(4)]
    seq_location = [None] * 4

    # Constraints for the sequence
    for i in range(4):
        # The i-th meeting in the sequence is friend_names[order[i]]
        s.add(Or([order[i] == j for j in range(4)]))
        for j in range(4):
            s.add(Implies(order[i] == j, seq_start[i] == meeting_vars[friend_names[j]]['start']))
            s.add(Implies(order[i] == j, seq_end[i] == meeting_vars[friend_names[j]]['end']))
            s.add(Implies(order[i] == j, seq_location[i] == friends[friend_names[j]]['location']))

    # Now, add travel time constraints between consecutive meetings
    for i in range(3):
        # Travel from seq_location[i] to seq_location[i+1] takes travel_times[seq_location[i]][seq_location[i+1]] minutes
        # So, seq_start[i+1] >= seq_end[i] + travel_time
        # But since seq_location is symbolic, we need to encode this with implications.
        for loc1 in travel_times:
            for loc2 in travel_times[loc1]:
                s.add(Implies(
                    And(seq_location[i] == loc1, seq_location[i+1] == loc2),
                    seq_start[i+1] >= seq_end[i] + travel_times[loc1][loc2]
                ))

    # The first meeting's start time must be >= current_time (9:00 AM) + travel time from Haight-Ashbury to the first location
    for loc in travel_times[current_location]:
        s.add(Implies(
            seq_location[0] == loc,
            seq_start[0] >= time_to_minutes(*current_time) + travel_times[current_location][loc]
        ))

    # Check if all meetings can be scheduled
    if s.check() == sat:
        m = s.model()
        # Extract the order of meetings
        order_indices = [m.evaluate(order[i]).as_long() for i in range(4)]
        # Get the meetings in order
        scheduled_meetings = []
        for i in range(4):
            friend = friend_names[order_indices[i]]
            start = m.evaluate(meeting_vars[friend]['start']).as_long()
            end = m.evaluate(meeting_vars[friend]['end']).as_long()
            scheduled_meetings.append({
                'friend': friend,
                'start': start,
                'end': end,
                'location': friends[friend]['location']
            })

        # Sort by start time
        scheduled_meetings.sort(key=lambda x: x['start'])

        # Build itinerary
        itinerary = []
        for meeting in scheduled_meetings:
            start_h, start_m = minutes_to_time(meeting['start'])
            end_h, end_m = minutes_to_time(meeting['end'])
            itinerary.append({
                "action": "meet",
                "person": meeting['friend'],
                "start_time": f"{start_h:02d}:{start_m:02d}",
                "end_time": f"{end_h:02d}:{end_m:02d}"
            })

        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

result = solve_scheduling()
print(json.dumps(result, indent=2))