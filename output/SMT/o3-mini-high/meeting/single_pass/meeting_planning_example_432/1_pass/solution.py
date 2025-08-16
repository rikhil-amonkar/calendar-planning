from z3 import *

def solve_schedule():
    # Define friend data: available time windows (in minutes since midnight),
    # meeting durations (in minutes) and their meeting locations.
    persons = {
        "Joseph": {
            "location": "Fisherman's Wharf",
            "avail_start": 8 * 60,       # 08:00 → 480
            "avail_end": 17 * 60 + 30,   # 17:30 → 1050
            "duration": 90
        },
        "Jeffrey": {
            "location": "Bayview",
            "avail_start": 17 * 60 + 30, # 17:30 → 1050
            "avail_end": 21 * 60 + 30,   # 21:30 → 1290
            "duration": 60
        },
        "Kevin": {
            "location": "Mission District",
            "avail_start": 11 * 60 + 15, # 11:15 → 675
            "avail_end": 15 * 60 + 15,   # 15:15 → 915
            "duration": 30
        },
        "David": {
            "location": "Embarcadero",
            "avail_start": 8 * 60 + 15,  # 08:15 → 495
            "avail_end": 9 * 60,         # 09:00 → 540
            "duration": 30
        },
        "Barbara": {
            "location": "Financial District",
            "avail_start": 10 * 60 + 30, # 10:30 → 630
            "avail_end": 16 * 60 + 30,   # 16:30 → 990
            "duration": 15
        }
    }

    # Define the travel time (in minutes) between locations.
    # Note: these times are directional.
    travel = {
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Financial District"): 26,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Mission District"): 13,
        ("Bayview", "Embarcadero"): 19,
        ("Bayview", "Financial District"): 19,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Bayview"): 15,
        ("Mission District", "Embarcadero"): 19,
        ("Mission District", "Financial District"): 17,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Bayview"): 21,
        ("Embarcadero", "Mission District"): 20,
        ("Embarcadero", "Financial District"): 5,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Mission District"): 17,
        ("Financial District", "Embarcadero"): 4
    }

    # You start your day at Golden Gate Park at 09:00 (540 minutes)
    start_location = "Golden Gate Park"
    start_time = 9 * 60  # 540 minutes

    # Create an Optimize object; we want to maximize the number of meetings attended.
    opt = Optimize()

    # For each friend, create variables for the meeting start time and finish time,
    # and a Boolean to indicate if we schedule a meeting with that person.
    S = {}  # Start times
    F = {}  # Finish times
    scheduled = {}  # Boolean flags
    for person, data in persons.items():
        S[person] = Int(f"S_{person}")
        F[person] = Int(f"F_{person}")
        scheduled[person] = Bool(f"scheduled_{person}")
        
        # If scheduled, then the meeting must occur within the available window.
        # Also, the finish time equals the start time plus the required meeting duration.
        opt.add(Implies(scheduled[person], S[person] >= data["avail_start"]))
        opt.add(Implies(scheduled[person], F[person] <= data["avail_end"]))
        opt.add(Implies(scheduled[person], F[person] == S[person] + data["duration"]))
        
        # Even the first meeting must be reachable from the start location.
        # So if a meeting is scheduled, start time must be later than:
        # starting time + travel time from Golden Gate Park to that meeting's location.
        tt = travel.get((start_location, data["location"]), 0)
        opt.add(Implies(scheduled[person], S[person] >= start_time + tt))

    # For any two scheduled meetings, enforce that they do not overlap.
    # That is, for any two persons p and q, if both are scheduled, then either
    # meeting p comes before meeting q (including travel time between their locations)
    # or vice versa.
    persons_list = list(persons.keys())
    for i in range(len(persons_list)):
        for j in range(i+1, len(persons_list)):
            p1 = persons_list[i]
            p2 = persons_list[j]
            loc1 = persons[p1]["location"]
            loc2 = persons[p2]["location"]
            # Get travel times between the locations. (default to 0 if missing, but all pairs are provided)
            t_p1_to_p2 = travel.get((loc1, loc2), 0)
            t_p2_to_p1 = travel.get((loc2, loc1), 0)
            opt.add(
                Implies(And(scheduled[p1], scheduled[p2]),
                        Or(S[p2] >= F[p1] + t_p1_to_p2,
                           S[p1] >= F[p2] + t_p2_to_p1))
            )

    # Our goal: maximize the number of meetings scheduled.
    total_meetings = Sum([If(scheduled[p], 1, 0) for p in persons_list])
    opt.maximize(total_meetings)

    # Check for a solution.
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        # Helper function: convert minutes since midnight to "HH:MM" 24-hour string.
        def to_time(t):
            hours = t // 60
            minutes = t % 60
            return f"{hours:02d}:{minutes:02d}"
        
        for person in persons_list:
            if m.evaluate(scheduled[person]):
                start_val = m.evaluate(S[person]).as_long()
                end_val   = m.evaluate(F[person]).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": person,
                    "start_time": to_time(start_val),
                    "end_time": to_time(end_val)
                })
        # Order the itinerary by start time.
        itinerary.sort(key=lambda entry: entry["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

if __name__ == "__main__":
    result = solve_schedule()
    import json
    print("SOLUTION:")
    print(json.dumps(result, indent=2))