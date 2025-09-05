from z3 import *
import json

def minutes_to_time(m):
    # Convert minutes (integer) since midnight into a string "H:MM" (24-hour format)
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define meeting data for each friend. Times are in minutes from midnight.
    # For example, 9:00 AM = 540, 17:30 = 1050, etc.
    friends = {
        "Joseph": {
            "location": "Fisherman's Wharf",
            "avail_start": 480,   # 8:00
            "avail_end": 1050,    # 17:30
            "duration": 90
        },
        "Jeffrey": {
            "location": "Bayview",
            "avail_start": 1050,  # 17:30
            "avail_end": 1290,    # 21:30
            "duration": 60
        },
        "Kevin": {
            "location": "Mission District",
            "avail_start": 675,   # 11:15
            "avail_end": 915,     # 15:15
            "duration": 30
        },
        "David": {
            "location": "Embarcadero",
            "avail_start": 495,   # 8:15
            "avail_end": 540,     # 9:00
            "duration": 30
        },
        "Barbara": {
            "location": "Financial District",
            "avail_start": 630,   # 10:30
            "avail_end": 990,     # 16:30
            "duration": 15
        }
    }

    # Travel times (in minutes) as given (directed)
    travel_times = {
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

    # Arrival at Golden Gate Park at 9:00 (540 minutes)
    start_location = "Golden Gate Park"
    arrival_time = 540

    opt = Optimize()

    # Create decision variables:
    # For each friend, x indicates whether we schedule a meeting and s is meeting's start time.
    meet_vars = {}
    start_vars = {}
    for friend, data in friends.items():
        x = Bool(f"meet_{friend}")
        s = Int(f"start_{friend}")
        meet_vars[friend] = x
        start_vars[friend] = s
        
        # If meeting is scheduled, then the meeting must start at or after the friend's availability and
        # also after arriving from the starting position.
        opt.add(Implies(x, s >= data["avail_start"]))
        opt.add(Implies(x, s >= arrival_time + travel_times[(start_location, data["location"])]))
        # Meeting must finish before the end of the friend's availability.
        opt.add(Implies(x, s + data["duration"] <= data["avail_end"]))

    # Add ordering constraints for every pair of scheduled meetings.
    # If both meetings are scheduled, then one must occur before the other (including travel time).
    friend_list = list(friends.keys())
    n = len(friend_list)
    for i in range(n):
        for j in range(i+1, n):
            f1 = friend_list[i]
            f2 = friend_list[j]
            loc1 = friends[f1]["location"]
            loc2 = friends[f2]["location"]
            d1 = friends[f1]["duration"]
            d2 = friends[f2]["duration"]
            t12 = travel_times[(loc1, loc2)]
            t21 = travel_times[(loc2, loc1)]
            # If both meetings are scheduled, then either f1 is finished (plus travel) before f2's start,
            # or f2 is finished (plus travel) before f1's start.
            opt.add(
                Implies(
                    And(meet_vars[f1], meet_vars[f2]),
                    Or(start_vars[f1] + d1 + t12 <= start_vars[f2],
                       start_vars[f2] + d2 + t21 <= start_vars[f1])
                )
            )

    # Objective: maximize the number of meetings scheduled.
    total_meetings = Sum([If(meet_vars[f], 1, 0) for f in friends])
    opt.maximize(total_meetings)

    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for friend in friends:
            if is_true(model.evaluate(meet_vars[friend])):
                meeting_start = model.evaluate(start_vars[friend]).as_long()
                meeting_end = meeting_start + friends[friend]["duration"]
                scheduled_meetings.append({
                    "person": friend,
                    "location": friends[friend]["location"],
                    "start": meeting_start,
                    "end": meeting_end
                })
        # Sort scheduled meetings by start time.
        scheduled_meetings.sort(key=lambda m: m["start"])

        itinerary = []
        for m in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "location": m["location"],
                "person": m["person"],
                "start_time": minutes_to_time(m["start"]),
                "end_time": minutes_to_time(m["end"])
            })
        result = {"itinerary": itinerary}
    else:
        result = {"itinerary": []}

    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()