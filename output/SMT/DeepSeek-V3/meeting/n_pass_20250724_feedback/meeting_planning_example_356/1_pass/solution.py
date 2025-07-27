from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their availability
    friends = {
        "Barbara": {
            "location": "North Beach",
            "available_start": (13, 45),  # 1:45 PM
            "available_end": (20, 15),    # 8:15 PM
            "min_duration": 60            # minutes
        },
        "Margaret": {
            "location": "Presidio",
            "available_start": (10, 15),  # 10:15 AM
            "available_end": (15, 15),    # 3:15 PM
            "min_duration": 30            # minutes
        },
        "Kevin": {
            "location": "Haight-Ashbury",
            "available_start": (20, 0),   # 8:00 PM
            "available_end": (20, 45),    # 8:45 PM
            "min_duration": 30           # minutes
        },
        "Kimberly": {
            "location": "Union Square",
            "available_start": (7, 45),   # 7:45 AM
            "available_end": (16, 45),    # 4:45 PM
            "min_duration": 30            # minutes
        }
    }

    # Travel times between locations (in minutes)
    travel_times = {
        "Bayview": {
            "North Beach": 21,
            "Presidio": 31,
            "Haight-Ashbury": 19,
            "Union Square": 17
        },
        "North Beach": {
            "Bayview": 22,
            "Presidio": 17,
            "Haight-Ashbury": 18,
            "Union Square": 7
        },
        "Presidio": {
            "Bayview": 31,
            "North Beach": 18,
            "Haight-Ashbury": 15,
            "Union Square": 22
        },
        "Haight-Ashbury": {
            "Bayview": 18,
            "North Beach": 19,
            "Presidio": 15,
            "Union Square": 17
        },
        "Union Square": {
            "Bayview": 15,
            "North Beach": 10,
            "Presidio": 24,
            "Haight-Ashbury": 18
        }
    }

    # Current location and time
    current_location = "Bayview"
    current_time = (9, 0)  # 9:00 AM

    # Convert time to minutes since 9:00 AM (0 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 9 * 60  # 9:00 AM is 0

    # Convert minutes back to time
    def minutes_to_time(minutes):
        total_minutes = 9 * 60 + minutes
        h = total_minutes // 60
        m = total_minutes % 60
        return (h, m)

    # Variables for each meeting
    meetings = {}
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        duration_var = Int(f'duration_{name}')
        meetings[name] = {
            'start': start_var,
            'end': end_var,
            'duration': duration_var,
            'location': friends[name]['location'],
            'available_start': time_to_minutes(*friends[name]['available_start']),
            'available_end': time_to_minutes(*friends[name]['available_end']),
            'min_duration': friends[name]['min_duration']
        }
        # Constrain meeting within available window
        s.add(start_var >= meetings[name]['available_start'])
        s.add(end_var <= meetings[name]['available_end'])
        s.add(end_var == start_var + duration_var)
        s.add(duration_var >= meetings[name]['min_duration'])

    # Variables to indicate if a meeting is scheduled
    scheduled = {name: Bool(f'scheduled_{name}') for name in friends}
    for name in friends:
        s.add(Implies(scheduled[name], meetings[name]['start'] >= 0))
        s.add(Implies(Not(scheduled[name]), meetings[name]['start'] == -1))

    # Order of meetings (permutation)
    # We need to model the sequence of meetings with travel times
    # This is complex; instead, we'll try to find a feasible sequence by ordering constraints

    # Possible sequences (since there are 4 friends, 4! = 24 possible sequences)
    # We'll model the sequence as a list and add constraints for travel times

    # Since modeling all permutations is complex, we'll use a heuristic approach:
    # Try to meet friends in an order that allows meeting as many as possible

    # Let's try to meet Margaret first (since she's available earliest)
    # Then Kimberly, then Barbara, then Kevin

    # Define the order as a list of names
    order = ["Margaret", "Kimberly", "Barbara", "Kevin"]
    # Alternatively, we could iterate over possible orders, but for simplicity, we'll proceed with this order

    # Add constraints for travel times between meetings
    prev_location = "Bayview"
    prev_end = 0  # 9:00 AM is 0 minutes
    for i, name in enumerate(order):
        meet = meetings[name]
        loc = meet['location']
        travel_time = travel_times[prev_location][loc]
        s.add(Implies(scheduled[name], meet['start'] >= prev_end + travel_time))
        prev_location = loc
        prev_end = If(scheduled[name], meet['end'], prev_end)

    # Maximize the number of scheduled meetings
    total_scheduled = Sum([If(scheduled[name], 1, 0) for name in friends])
    s.maximize(total_scheduled)

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in friends:
            if model.evaluate(scheduled[name]):
                start_min = model.evaluate(meetings[name]['start']).as_long()
                end_min = model.evaluate(meetings[name]['end']).as_long()
                start_time = minutes_to_time(start_min)
                end_time = minutes_to_time(end_min)
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start_time[0]:02d}:{start_time[1]:02d}",
                    "end_time": f"{end_time[0]:02d}:{end_time[1]:02d}"
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))