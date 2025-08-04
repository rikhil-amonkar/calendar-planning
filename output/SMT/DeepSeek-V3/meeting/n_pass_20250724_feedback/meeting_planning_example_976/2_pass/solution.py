from z3 import *
import json

def solve_scheduling_problem():
    # Initialize the solver
    s = Optimize()

    # Define the travel times between locations (in minutes)
    travel_times = {
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Union Square'): 10,
        ('Embarcadero', 'The Castro'): 25,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Marina District'): 12,
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'Nob Hill'): 20,
        ('Bayview', 'Presidio'): 32,
        ('Bayview', 'Union Square'): 18,
        ('Bayview', 'The Castro'): 19,
        ('Bayview', 'North Beach'): 22,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Marina District'): 27,
        ('Chinatown', 'Embarcadero'): 5,
        ('Chinatown', 'Bayview'): 20,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Nob Hill'): 9,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Fisherman\'s Wharf'): 8,
        ('Chinatown', 'Marina District'): 12,
        ('Alamo Square', 'Embarcadero'): 16,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Chinatown'): 15,
        ('Alamo Square', 'Nob Hill'): 11,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'Marina District'): 15,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Nob Hill', 'Bayview'): 19,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Alamo Square'): 11,
        ('Nob Hill', 'Presidio'): 17,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Fisherman\'s Wharf'): 10,
        ('Nob Hill', 'Marina District'): 11,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Alamo Square'): 19,
        ('Presidio', 'Nob Hill'): 18,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'The Castro'): 21,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Presidio', 'Marina District'): 11,
        ('Union Square', 'Embarcadero'): 11,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Nob Hill'): 9,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'The Castro'): 17,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Fisherman\'s Wharf'): 15,
        ('Union Square', 'Marina District'): 18,
        ('The Castro', 'Embarcadero'): 22,
        ('The Castro', 'Bayview'): 19,
        ('The Castro', 'Chinatown'): 22,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Presidio'): 20,
        ('The Castro', 'Union Square'): 19,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Fisherman\'s Wharf'): 24,
        ('The Castro', 'Marina District'): 21,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'Bayview'): 25,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'The Castro'): 23,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'Marina District'): 9,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Chinatown'): 12,
        ('Fisherman\'s Wharf', 'Alamo Square'): 21,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11,
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Union Square'): 13,
        ('Fisherman\'s Wharf', 'The Castro'): 27,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Fisherman\'s Wharf', 'Marina District'): 9,
        ('Marina District', 'Embarcadero'): 14,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Alamo Square'): 15,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Presidio'): 10,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'The Castro'): 22,
        ('Marina District', 'North Beach'): 11,
        ('Marina District', 'Fisherman\'s Wharf'): 10,
    }

    # Define the friends and their availability
    friends = [
        {"name": "Matthew", "location": "Bayview", "start": 19*60 + 15, "end": 22*60, "duration": 120},
        {"name": "Karen", "location": "Chinatown", "start": 19*60 + 15, "end": 21*60 + 15, "duration": 90},
        {"name": "Sarah", "location": "Alamo Square", "start": 20*60, "end": 21*60 + 45, "duration": 105},
        {"name": "Jessica", "location": "Nob Hill", "start": 16*60 + 30, "end": 18*60 + 45, "duration": 120},
        {"name": "Stephanie", "location": "Presidio", "start": 7*60 + 30, "end": 10*60 + 15, "duration": 60},
        {"name": "Mary", "location": "Union Square", "start": 16*60 + 45, "end": 21*60 + 30, "duration": 60},
        {"name": "Charles", "location": "The Castro", "start": 16*60 + 30, "end": 22*60, "duration": 105},
        {"name": "Nancy", "location": "North Beach", "start": 14*60 + 45, "end": 20*60, "duration": 15},
        {"name": "Thomas", "location": "Fisherman\'s Wharf", "start": 13*60 + 30, "end": 19*60, "duration": 30},
        {"name": "Brian", "location": "Marina District", "start": 12*60 + 15, "end": 18*60, "duration": 60},
    ]

    # Current location starts at Embarcadero at 9:00 AM (540 minutes)
    current_location = "Embarcadero"
    current_time = 9 * 60  # 9:00 AM in minutes

    # Create variables for each meeting
    meetings = []
    for friend in friends:
        start_var = Int(f"start_{friend['name']}")
        end_var = Int(f"end_{friend['name']}")
        s.add(start_var >= friend["start"])
        s.add(end_var <= friend["end"])
        s.add(end_var - start_var >= friend["duration"])
        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start_var": start_var,
            "end_var": end_var,
            "duration": friend["duration"]
        })

    # Add constraints to ensure no overlapping meetings and travel times
    for i in range(len(meetings)):
        for j in range(i + 1, len(meetings)):
            m1 = meetings[i]
            m2 = meetings[j]
            # Either m1 is before m2 or m2 is before m1, considering travel time
            travel_time = travel_times.get((m1["location"], m2["location"]), 0)
            s.add(Or(
                m1["end_var"] + travel_time <= m2["start_var"],
                m2["end_var"] + travel_time <= m1["start_var"]
            ))

    # Ensure the first meeting is after the current time plus travel time
    for meeting in meetings:
        travel_time = travel_times.get((current_location, meeting["location"]), 0)
        s.add(meeting["start_var"] >= current_time + travel_time)

    # Maximize the number of friends met
    s.maximize(Sum([If(And(meeting["start_var"] >= 0, meeting["end_var"] >= 0), 1, 0) for meeting in meetings]))

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for meeting in meetings:
            start = model.evaluate(meeting["start_var"])
            end = model.evaluate(meeting["end_var"])
            if start.as_long() != 0 and end.as_long() != 0:
                start_time = f"{start.as_long() // 60:02d}:{start.as_long() % 60:02d}"
                end_time = f"{end.as_long() // 60:02d}:{end.as_long() % 60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": meeting["name"],
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: (int(x["start_time"][:2]), int(x["start_time"][3:])))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))