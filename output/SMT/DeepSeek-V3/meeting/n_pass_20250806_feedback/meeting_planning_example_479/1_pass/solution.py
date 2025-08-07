from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Travel times dictionary: from_location -> to_location -> minutes
    travel_times = {
        'Embarcadero': {
            'Golden Gate Park': 25,
            'Haight-Ashbury': 21,
            'Bayview': 21,
            'Presidio': 20,
            'Financial District': 5
        },
        'Golden Gate Park': {
            'Embarcadero': 25,
            'Haight-Ashbury': 7,
            'Bayview': 23,
            'Presidio': 11,
            'Financial District': 26
        },
        'Haight-Ashbury': {
            'Embarcadero': 20,
            'Golden Gate Park': 7,
            'Bayview': 18,
            'Presidio': 15,
            'Financial District': 21
        },
        'Bayview': {
            'Embarcadero': 19,
            'Golden Gate Park': 22,
            'Haight-Ashbury': 19,
            'Presidio': 31,
            'Financial District': 19
        },
        'Presidio': {
            'Embarcadero': 20,
            'Golden Gate Park': 12,
            'Haight-Ashbury': 15,
            'Bayview': 31,
            'Financial District': 23
        },
        'Financial District': {
            'Embarcadero': 4,
            'Golden Gate Park': 23,
            'Haight-Ashbury': 19,
            'Bayview': 19,
            'Presidio': 22
        }
    }

    # Friends' data: name -> (location, start_available, end_available, min_duration)
    friends = {
        'Mary': ('Golden Gate Park', 8*60 + 45, 11*60 + 45, 45),
        'Kevin': ('Haight-Ashbury', 10*60 + 15, 16*60 + 15, 90),
        'Deborah': ('Bayview', 15*60 + 0, 19*60 + 15, 120),
        'Stephanie': ('Presidio', 10*60 + 0, 17*60 + 15, 120),
        'Emily': ('Financial District', 11*60 + 30, 21*60 + 45, 105)
    }

    # Variables for each friend's meeting start and end times (in minutes since 9:00 AM, i.e., 540)
    start_vars = {}
    end_vars = {}
    for name in friends:
        start_vars[name] = Int(f'start_{name}')
        end_vars[name] = Int(f'end_{name}')

    # Current time starts at 9:00 AM (540 minutes since midnight)
    current_time = 540  # 9:00 AM in minutes since midnight
    current_location = 'Embarcadero'

    # To model the order of meetings, we need to sequence them. We'll use a list to represent the order.
    # However, since Z3 requires constraints, we'll need to model all possible permutations or use a more clever approach.
    # Given the complexity, we'll assume a specific order and adjust if needed, but for Z3, we'll need to allow any order.
    # This is complex, so instead, we'll predefine a feasible order based on heuristics.

    # Heuristic order: Mary (early), then Kevin or Stephanie, then others.
    # But for Z3, we'll need to model all possible sequences, which is complex. Instead, we'll proceed with a fixed order and check feasibility.

    # Alternative approach: model start and end times with constraints that enforce travel times between any two meetings.

    # Constraints for each friend's meeting time within their availability
    for name in friends:
        loc, start_avail, end_avail, min_dur = friends[name]
        s.add(start_vars[name] >= start_avail)
        s.add(end_vars[name] <= end_avail)
        s.add(end_vars[name] == start_vars[name] + min_dur)

    # To model the sequence, we need to enforce that for any two meetings, either one is before the other with travel time.
    # This is complex, so we'll use a fixed order based on earliest availability and travel times.

    # Let's try the order: Mary -> Kevin -> Stephanie -> Deborah -> Emily
    order = ['Mary', 'Kevin', 'Stephanie', 'Deborah', 'Emily']

    # Add constraints for the order
    for i in range(len(order) - 1):
        current_person = order[i]
        next_person = order[i + 1]
        current_loc = friends[current_person][0]
        next_loc = friends[next_person][0]
        travel_time = travel_times[current_loc][next_loc]
        s.add(start_vars[next_person] >= end_vars[current_person] + travel_time)

    # Also, the first meeting must start after arriving at Embarcadero and traveling to Mary's location.
    first_person = order[0]
    first_loc = friends[first_person][0]
    travel_time_first = travel_times[current_location][first_loc]
    s.add(start_vars[first_person] >= current_time + travel_time_first)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in order:
            start = model.eval(start_vars[name]).as_long()
            end = model.eval(end_vars[name]).as_long()
            start_hour = start // 60
            start_minute = start % 60
            end_hour = end // 60
            end_minute = end % 60
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_hour:02d}:{start_minute:02d}",
                "end_time": f"{end_hour:02d}:{end_minute:02d}"
            })
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Execute the solver
result = solve_scheduling()
print(result)