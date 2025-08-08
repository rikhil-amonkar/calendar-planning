from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define travel times (in minutes) between locations
    travel_times = {
        ('Richmond District', 'Chinatown'): 20,
        ('Richmond District', 'Sunset District'): 11,
        ('Richmond District', 'Alamo Square'): 13,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'Embarcadero'): 19,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Richmond District', 'Bayview'): 27,
        ('Chinatown', 'Richmond District'): 20,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Embarcadero'): 5,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Bayview'): 20,
        ('Sunset District', 'Richmond District'): 12,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Financial District'): 30,
        ('Sunset District', 'North Beach'): 28,
        ('Sunset District', 'Embarcadero'): 30,
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Bayview'): 22,
        ('Alamo Square', 'Richmond District'): 11,
        ('Alamo Square', 'Chinatown'): 15,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'Financial District'): 17,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Embarcadero'): 16,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Bayview'): 16,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Sunset District'): 30,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Bayview'): 19,
        ('North Beach', 'Richmond District'): 18,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Sunset District'): 27,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Bayview'): 25,
        ('Embarcadero', 'Richmond District'): 21,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Sunset District'): 30,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Embarcadero', 'Financial District'): 5,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Bayview'): 21,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'Alamo Square'): 19,
        ('Presidio', 'Financial District'): 23,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Bayview'): 31,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Alamo Square'): 9,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'North Beach'): 23,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Sunset District'): 23,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'Financial District'): 19,
        ('Bayview', 'North Beach'): 22,
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Presidio'): 32,
        ('Bayview', 'Golden Gate Park'): 22,
    }

    # Friends' data: name, location, available from, available to, min duration (in minutes)
    friends = [
        ("Robert", "Chinatown", (7, 45), (17, 30), 120),
        ("David", "Sunset District", (12, 30), (19, 45), 45),
        ("Matthew", "Alamo Square", (8, 45), (13, 45), 90),
        ("Jessica", "Financial District", (9, 30), (18, 45), 45),
        ("Melissa", "North Beach", (7, 15), (16, 45), 45),
        ("Mark", "Embarcadero", (15, 15), (17, 0), 45),
        ("Deborah", "Presidio", (19, 0), (19, 45), 45),
        ("Karen", "Golden Gate Park", (19, 30), (22, 0), 120),
        ("Laura", "Bayview", (21, 15), (22, 15), 15),
    ]

    # Convert time to minutes since midnight for easier handling
    def time_to_minutes(h, m):
        return h * 60 + m

    friends_availability = []
    for name, loc, (start_h, start_m), (end_h, end_m), min_dur in friends:
        start_min = time_to_minutes(start_h, start_m)
        end_min = time_to_minutes(end_h, end_m)
        friends_availability.append((name, loc, start_min, end_min, min_dur))

    # Variables for each meeting: start and end times (in minutes since midnight)
    meeting_vars = []
    for i, (name, loc, start_min, end_min, min_dur) in enumerate(friends_availability):
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meeting_vars.append((name, loc, start, end, min_dur))
        # Constraints: meeting within availability and duration
        s.add(start >= start_min)
        s.add(end <= end_min)
        s.add(end >= start + min_dur)

    # Initial location: Richmond District at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_loc = "Richmond District"

    # Ensure meetings are scheduled in some order with travel times
    # We need to sequence the meetings. For simplicity, we'll assume a specific order based on earliest possible start times.
    # However, in a more sophisticated model, we would use a more dynamic approach with additional variables for ordering.

    # For this problem, we'll prioritize meeting friends with tighter time windows first.
    # Let's try meeting Matthew first (Alamo Square, available until 1:45 PM)
    # Then, we can proceed to others like Robert, David, etc.

    # We'll manually sequence the meetings to meet as many as possible.
    # Alternatively, we could use a more complex model with sequencing variables, but for brevity, we'll proceed with a feasible sequence.

    # Meeting Matthew first
    matthew_idx = next(i for i, (name, _, _, _, _) in enumerate(meeting_vars) if name == "Matthew")
    name, loc, start, end, min_dur = meeting_vars[matthew_idx]
    travel = travel_times[(current_loc, loc)]
    s.add(start >= current_time + travel)
    current_time = end
    current_loc = loc

    # Next, meet Jessica (Financial District)
    jessica_idx = next(i for i, (name, _, _, _, _) in enumerate(meeting_vars) if name == "Jessica")
    name, loc, start, end, min_dur = meeting_vars[jessica_idx]
    travel = travel_times[(current_loc, loc)]
    s.add(start >= current_time + travel)
    current_time = end
    current_loc = loc

    # Next, meet Robert (Chinatown)
    robert_idx = next(i for i, (name, _, _, _, _) in enumerate(meeting_vars) if name == "Robert")
    name, loc, start, end, min_dur = meeting_vars[robert_idx]
    travel = travel_times[(current_loc, loc)]
    s.add(start >= current_time + travel)
    current_time = end
    current_loc = loc

    # Next, meet David (Sunset District)
    david_idx = next(i for i, (name, _, _, _, _) in enumerate(meeting_vars) if name == "David")
    name, loc, start, end, min_dur = meeting_vars[david_idx]
    travel = travel_times[(current_loc, loc)]
    s.add(start >= current_time + travel)
    current_time = end
    current_loc = loc

    # Next, meet Mark (Embarcadero)
    mark_idx = next(i for i, (name, _, _, _, _) in enumerate(meeting_vars) if name == "Mark")
    name, loc, start, end, min_dur = meeting_vars[mark_idx]
    travel = travel_times[(current_loc, loc)]
    s.add(start >= current_time + travel)
    current_time = end
    current_loc = loc

    # Next, meet Deborah (Presidio)
    deborah_idx = next(i for i, (name, _, _, _, _) in enumerate(meeting_vars) if name == "Deborah")
    name, loc, start, end, min_dur = meeting_vars[deborah_idx]
    travel = travel_times[(current_loc, loc)]
    s.add(start >= current_time + travel)
    current_time = end
    current_loc = loc

    # Next, meet Karen (Golden Gate Park)
    karen_idx = next(i for i, (name, _, _, _, _) in enumerate(meeting_vars) if name == "Karen")
    name, loc, start, end, min_dur = meeting_vars[karen_idx]
    travel = travel_times[(current_loc, loc)]
    s.add(start >= current_time + travel)
    current_time = end
    current_loc = loc

    # Finally, meet Laura (Bayview)
    laura_idx = next(i for i, (name, _, _, _, _) in enumerate(meeting_vars) if name == "Laura")
    name, loc, start, end, min_dur = meeting_vars[laura_idx]
    travel = travel_times[(current_loc, loc)]
    s.add(start >= current_time + travel)

    # Check if the solver can find a feasible solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name, loc, start, end, min_dur in meeting_vars:
            start_val = model.evaluate(start).as_long()
            end_val = model.evaluate(end).as_long()
            start_h = start_val // 60
            start_m = start_val % 60
            end_h = end_val // 60
            end_m = end_val % 60
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_h:02d}:{start_m:02d}",
                "end_time": f"{end_h:02d}:{end_m:02d}"
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:5]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the solver and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))