from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    solver = Solver()

    # Define the locations and their travel times
    locations = {
        'Financial District': 0,
        'Golden Gate Park': 1,
        'Chinatown': 2,
        'Union Square': 3,
        'Fisherman\'s Wharf': 4,
        'Pacific Heights': 5,
        'North Beach': 6
    }

    # Travel times matrix (from_location, to_location) -> minutes
    travel_times = {
        (0, 1): 23,
        (0, 2): 5,
        (0, 3): 9,
        (0, 4): 10,
        (0, 5): 13,
        (0, 6): 7,
        (1, 0): 26,
        (1, 2): 23,
        (1, 3): 22,
        (1, 4): 24,
        (1, 5): 16,
        (1, 6): 24,
        (2, 0): 5,
        (2, 1): 23,
        (2, 3): 7,
        (2, 4): 8,
        (2, 5): 10,
        (2, 6): 3,
        (3, 0): 9,
        (3, 1): 22,
        (3, 2): 7,
        (3, 4): 15,
        (3, 5): 15,
        (3, 6): 10,
        (4, 0): 11,
        (4, 1): 25,
        (4, 2): 12,
        (4, 3): 13,
        (4, 5): 12,
        (4, 6): 6,
        (5, 0): 13,
        (5, 1): 15,
        (5, 2): 11,
        (5, 3): 12,
        (5, 4): 13,
        (5, 6): 9,
        (6, 0): 8,
        (6, 1): 22,
        (6, 2): 6,
        (6, 3): 7,
        (6, 4): 5,
        (6, 5): 8
    }

    # Friends' information
    friends = [
        {'name': 'Stephanie', 'location': 'Golden Gate Park', 'start': 11*60, 'end': 15*60, 'min_duration': 105},
        {'name': 'Karen', 'location': 'Chinatown', 'start': 13*60 + 45, 'end': 16*60 + 30, 'min_duration': 15},
        {'name': 'Brian', 'location': 'Union Square', 'start': 15*60, 'end': 17*60 + 15, 'min_duration': 30},
        {'name': 'Rebecca', 'location': 'Fisherman\'s Wharf', 'start': 8*60, 'end': 11*60 + 15, 'min_duration': 30},
        {'name': 'Joseph', 'location': 'Pacific Heights', 'start': 8*60 + 15, 'end': 9*60 + 30, 'min_duration': 60},
        {'name': 'Steven', 'location': 'North Beach', 'start': 14*60 + 30, 'end': 20*60 + 45, 'min_duration': 120}
    ]

    # Current location starts at Financial District at 9:00 AM (540 minutes)
    current_location = locations['Financial District']
    current_time = 9 * 60

    # Variables for each meeting
    meetings = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        duration = Int(f"duration_{friend['name']}")
        location = locations[friend['location']]
        meetings.append({
            'name': friend['name'],
            'start': start,
            'end': end,
            'duration': duration,
            'location': location,
            'friend': friend
        })

    # Constraints for each meeting
    for meeting in meetings:
        friend = meeting['friend']
        solver.add(meeting['start'] >= friend['start'])
        solver.add(meeting['end'] <= friend['end'])
        solver.add(meeting['duration'] >= friend['min_duration'])
        solver.add(meeting['end'] == meeting['start'] + meeting['duration'])

    # Order constraints and travel times
    for i in range(len(meetings)):
        for j in range(i + 1, len(meetings)):
            # Either meeting i is before meeting j or vice versa
            before = And(
                meetings[i]['end'] + travel_times[(meetings[i]['location'], meetings[j]['location'])] <= meetings[j]['start'],
                meetings[j]['start'] >= current_time + travel_times[(current_location, meetings[j]['location'])]
            )
            after = And(
                meetings[j]['end'] + travel_times[(meetings[j]['location'], meetings[i]['location'])] <= meetings[i]['start'],
                meetings[i]['start'] >= current_time + travel_times[(current_location, meetings[i]['location'])]
            )
            solver.add(Or(before, after))

    # Ensure all meetings are scheduled after current_time
    for meeting in meetings:
        solver.add(meeting['start'] >= current_time + travel_times[(current_location, meeting['location'])])

    # Maximize the number of friends met
    # We can also maximize the total time spent with friends, but here we prioritize meeting all if possible
    # Check if all meetings can be scheduled
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for meeting in meetings:
            start = model.evaluate(meeting['start']).as_long()
            end = model.evaluate(meeting['end']).as_long()
            start_h = start // 60
            start_m = start % 60
            end_h = end // 60
            end_m = end % 60
            itinerary.append({
                "action": "meet",
                "person": meeting['name'],
                "start_time": f"{start_h:02d}:{start_m:02d}",
                "end_time": f"{end_h:02d}:{end_m:02d}"
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:])))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))