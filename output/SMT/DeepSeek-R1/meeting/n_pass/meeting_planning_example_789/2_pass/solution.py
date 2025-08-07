from z3 import *
import json

def main():
    # Data setup
    friends = ['Betty', 'Melissa', 'Joshua', 'Jeffrey', 'James', 'Anthony', 'Timothy', 'Emily']
    locations = {
        'Betty': 'Russian Hill',
        'Melissa': 'Alamo Square',
        'Joshua': 'Haight-Ashbury',
        'Jeffrey': 'Marina District',
        'James': 'Bayview',
        'Anthony': 'Chinatown',
        'Timothy': 'Presidio',
        'Emily': 'Sunset District'
    }
    durations = {
        'Betty': 105,
        'Melissa': 105,
        'Joshua': 90,
        'Jeffrey': 45,
        'James': 90,
        'Anthony': 75,
        'Timothy': 90,
        'Emily': 120
    }
    available_start = {
        'Betty': 7 * 60,        # 420 minutes (7:00 AM)
        'Melissa': 9 * 60 + 30,  # 570 minutes (9:30 AM)
        'Joshua': 12 * 60 + 15,  # 735 minutes (12:15 PM)
        'Jeffrey': 12 * 60 + 15, # 735 minutes (12:15 PM)
        'James': 7 * 60 + 30,    # 450 minutes (7:30 AM)
        'Anthony': 11 * 60 + 45, # 705 minutes (11:45 AM)
        'Timothy': 12 * 60 + 30, # 750 minutes (12:30 PM)
        'Emily': 19 * 60 + 30    # 1170 minutes (7:30 PM)
    }
    available_end = {
        'Betty': 16 * 60 + 45,  # 1005 minutes (4:45 PM)
        'Melissa': 17 * 60 + 15, # 1035 minutes (5:15 PM)
        'Joshua': 19 * 60,       # 1140 minutes (7:00 PM)
        'Jeffrey': 18 * 60,      # 1080 minutes (6:00 PM)
        'James': 20 * 60,        # 1200 minutes (8:00 PM)
        'Anthony': 13 * 60 + 30, # 810 minutes (1:30 PM)
        'Timothy': 14 * 60 + 45, # 885 minutes (2:45 PM)
        'Emily': 21 * 60 + 30    # 1290 minutes (9:30 PM)
    }
    travel_time = {
        "Union Square": {
            "Russian Hill": 13,
            "Alamo Square": 15,
            "Haight-Ashbury": 18,
            "Marina District": 18,
            "Bayview": 15,
            "Chinatown": 7,
            "Presidio": 24,
            "Sunset District": 27
        },
        "Russian Hill": {
            "Union Square": 10,
            "Alamo Square": 15,
            "Haight-Ashbury": 17,
            "Marina District": 7,
            "Bayview": 23,
            "Chinatown": 9,
            "Presidio": 14,
            "Sunset District": 23
        },
        "Alamo Square": {
            "Union Square": 14,
            "Russian Hill": 13,
            "Haight-Ashbury": 5,
            "Marina District": 15,
            "Bayview": 16,
            "Chinatown": 15,
            "Presidio": 17,
            "Sunset District": 16
        },
        "Haight-Ashbury": {
            "Union Square": 19,
            "Russian Hill": 17,
            "Alamo Square": 5,
            "Marina District": 17,
            "Bayview": 18,
            "Chinatown": 19,
            "Presidio": 15,
            "Sunset District": 15
        },
        "Marina District": {
            "Union Square": 16,
            "Russian Hill": 8,
            "Alamo Square": 15,
            "Haight-Ashbury": 16,
            "Bayview": 27,
            "Chinatown": 15,
            "Presidio": 10,
            "Sunset District": 19
        },
        "Bayview": {
            "Union Square": 18,
            "Russian Hill": 23,
            "Alamo Square": 16,
            "Haight-Ashbury": 19,
            "Marina District": 27,
            "Chinatown": 19,
            "Presidio": 32,
            "Sunset District": 23
        },
        "Chinatown": {
            "Union Square": 7,
            "Russian Hill": 7,
            "Alamo Square": 17,
            "Haight-Ashbury": 19,
            "Marina District": 12,
            "Bayview": 20,
            "Presidio": 19,
            "Sunset District": 29
        },
        "Presidio": {
            "Union Square": 22,
            "Russian Hill": 14,
            "Alamo Square": 19,
            "Haight-Ashbury": 15,
            "Marina District": 11,
            "Bayview": 31,
            "Chinatown": 21,
            "Sunset District": 15
        },
        "Sunset District": {
            "Union Square": 30,
            "Russian Hill": 24,
            "Alamo Square": 17,
            "Haight-Ashbury": 15,
            "Marina District": 21,
            "Bayview": 22,
            "Chinatown": 30,
            "Presidio": 16
        }
    }

    emily_index = friends.index('Emily')
    start_location = "Union Square"
    start_time = 9 * 60  # 9:00 AM in minutes from midnight (540)

    # Create Z3 solver
    solver = Solver()
    solver.set("timeout", 300000)  # 5 minutes timeout

    # Define variables: order of meetings and start times
    n = len(friends)
    order = [Int(f'order_{i}') for i in range(n)]
    starts = [Int(f'start_{i}') for i in range(n)]

    # Order constraints: each order[i] is between 0 and n-1, distinct, and last is Emily
    solver.add([And(order[i] >= 0, order[i] < n) for i in range(n)])
    solver.add(Distinct(order))
    solver.add(order[n-1] == emily_index)

    # Constraint: Emily's meeting starts at 1170
    solver.add(starts[emily_index] == 1170)

    # Availability constraints for each friend
    for i in range(n):
        friend = friends[i]
        solver.add(starts[i] >= available_start[friend])
        solver.add(starts[i] + durations[friend] <= available_end[friend])

    # Travel constraints
    for k in range(n):
        if k == 0:
            # First meeting: travel from start_location to the meeting's location
            idx0 = order[0]
            loc0 = locations[friends[idx0]]
            solver.add(starts[idx0] >= start_time + travel_time[start_location][loc0])
        else:
            # Travel from the previous meeting to the current
            idx_prev = order[k-1]
            idx_curr = order[k]
            loc_prev = locations[friends[idx_prev]]
            loc_curr = locations[friends[idx_curr]]
            solver.add(starts[idx_curr] >= starts[idx_prev] + durations[friends[idx_prev]] + travel_time[loc_prev][loc_curr])

    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        # Extract start times
        start_times = {}
        for i in range(n):
            start_val = model.evaluate(starts[i]).as_long()
            start_times[friends[i]] = start_val

        # Build itinerary sorted by start time
        itinerary = []
        for friend in friends:
            start_minutes = start_times[friend]
            end_minutes = start_minutes + durations[friend]
            # Convert to HH:MM
            start_hour = start_minutes // 60
            start_minute = start_minutes % 60
            end_hour = end_minutes // 60
            end_minute = end_minutes % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": start_str,
                "end_time": end_str
            })
        
        # Sort by start time (using string sort since times are HH:MM with leading zeros)
        itinerary.sort(key=lambda x: x['start_time'])
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()