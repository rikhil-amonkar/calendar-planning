from z3 import *
import json

def solve_scheduling():
    # Initialize solver with optimization
    s = Optimize()

    # Friends data with locations and time windows
    friends = {
        "Stephanie": {"location": "Richmond District", "start": (16, 15), "end": (21, 30), "min_duration": 75},
        "William": {"location": "Union Square", "start": (10, 45), "end": (17, 30), "min_duration": 45},
        "Elizabeth": {"location": "Nob Hill", "start": (12, 15), "end": (15, 0), "min_duration": 105},
        "Joseph": {"location": "Fisherman's Wharf", "start": (12, 45), "end": (14, 0), "min_duration": 75},
        "Anthony": {"location": "Golden Gate Park", "start": (13, 0), "end": (20, 30), "min_duration": 75},
        "Barbara": {"location": "Embarcadero", "start": (19, 15), "end": (20, 30), "min_duration": 75},
        "Carol": {"location": "Financial District", "start": (11, 45), "end": (16, 15), "min_duration": 60},
        "Sandra": {"location": "North Beach", "start": (10, 0), "end": (12, 30), "min_duration": 15},
        "Kenneth": {"location": "Presidio", "start": (21, 15), "end": (22, 15), "min_duration": 45}
    }

    # Travel times between locations
    travel_times = {
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Presidio"): 10,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Presidio"): 7,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Presidio"): 24,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Presidio"): 17,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Presidio"): 11,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Presidio"): 20,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Presidio"): 22,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Presidio"): 17,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "North Beach"): 18
    }

    # Convert time to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 540

    # Create variables and basic constraints
    meeting_vars = {}
    for name in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meeting_vars[name] = (start, end)
        s.add(end - start >= friends[name]["min_duration"])
        s.add(start >= time_to_minutes(*friends[name]["start"]))
        s.add(end <= time_to_minutes(*friends[name]["end"]))

    # Current location starts at Marina District
    current_location = "Marina District"

    # Create meeting sequence variables
    meeting_order = [name for name in friends]
    sequence = [Int(f'seq_{i}') for i in range(len(meeting_order))]
    s.add(Distinct(sequence))
    for i in range(len(sequence)):
        s.add(sequence[i] >= 0, sequence[i] < len(meeting_order))

    # Add travel time constraints between consecutive meetings
    for i in range(len(sequence)-1):
        current = sequence[i]
        next_ = sequence[i+1]
        for j in range(len(meeting_order)):
            for k in range(len(meeting_order)):
                s.add(Implies(And(current == j, next_ == k),
                      meeting_vars[meeting_order[k]][0] >= 
                      meeting_vars[meeting_order[j]][1] + 
                      travel_times[(friends[meeting_order[j]]["location"], 
                                  friends[meeting_order[k]]["location"]))

    # First meeting must be reachable from Marina District
    first = sequence[0]
    for j in range(len(meeting_order)):
        s.add(Implies(first == j,
                     meeting_vars[meeting_order[j]][0] >= 
                     travel_times[(current_location, 
                                 friends[meeting_order[j]]["location"]))

    # Maximize number of meetings scheduled
    scheduled = [Bool(f'scheduled_{name}') for name in friends]
    for name in friends:
        s.add(Implies(scheduled[meeting_order.index(name)],
                     And(meeting_vars[name][0] >= 0,
                         meeting_vars[name][1] <= time_to_minutes(23, 59))))

    s.maximize(Sum([If(scheduled[i], 1, 0) for i in range(len(scheduled))]))

    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        # Get the meeting order from the model
        ordered_meetings = sorted([(model.evaluate(sequence[i]).as_long(), meeting_order[i]) 
                                 for i in range(len(sequence))], key=lambda x: x[0])
        for _, name in ordered_meetings:
            if is_true(model.evaluate(scheduled[meeting_order.index(name)])):
                start = model.evaluate(meeting_vars[name][0]).as_long()
                end = model.evaluate(meeting_vars[name][1]).as_long()
                start_h = (start + 540) // 60
                start_m = (start + 540) % 60
                end_h = (end + 540) // 60
                end_m = (end + 540) % 60
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start_h:02d}:{start_m:02d}",
                    "end_time": f"{end_h:02d}:{end_m:02d}"
                })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the solver
result = solve_scheduling()
print(json.dumps(result, indent=2))