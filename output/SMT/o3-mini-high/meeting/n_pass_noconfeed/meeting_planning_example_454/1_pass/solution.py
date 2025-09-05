import json
from z3 import Optimize, Int, Implies, Distinct, sat

def minutes_to_time(m):
    # Convert integer minutes to H:MM format (24-hour, no leading zero for hours)
    h = m // 60
    m_rem = m % 60
    return f"{h}:{m_rem:02d}"

def main():
    # Travel times between locations (in minutes)
    travel = {
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Mission District"): 26,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Mission District"): 17,
        ("Bayview", "Presidio"): 31,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "Chinatown"): 18,
        ("Bayview", "North Beach"): 21,
        ("Bayview", "Mission District"): 13,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Bayview"): 22,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Mission District"): 18,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Bayview"): 22,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Mission District"): 18,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Bayview"): 15,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "North Beach"): 17
    }
    
    # Friend meeting constraints
    # Times are represented in minutes from midnight.
    # For example, 9:00 AM = 9*60 = 540.
    # Available windows and minimum meeting durations (in minutes) are given.
    friends = [
        {
            "name": "Jessica",
            "location": "Golden Gate Park",
            "avail_start": 13*60 + 45,  # 13:45 -> 825
            "avail_end": 15*60,         # 15:00 -> 900
            "min_duration": 30
        },
        {
            "name": "Ashley",
            "location": "Bayview",
            "avail_start": 17*60 + 15,  # 17:15 -> 1035
            "avail_end": 20*60,         # 20:00 -> 1200
            "min_duration": 105
        },
        {
            "name": "Ronald",
            "location": "Chinatown",
            "avail_start": 7*60 + 15,   # 7:15 -> 435
            "avail_end": 14*60 + 45,    # 14:45 -> 885
            "min_duration": 90
        },
        {
            "name": "William",
            "location": "North Beach",
            "avail_start": 13*60 + 15,  # 13:15 -> 795
            "avail_end": 20*60 + 15,    # 20:15 -> 1215
            "min_duration": 15
        },
        {
            "name": "Daniel",
            "location": "Mission District",
            "avail_start": 7*60,        # 7:00 -> 420
            "avail_end": 11*60 + 15,      # 11:15 -> 675
            "min_duration": 105
        }
    ]
    
    opt = Optimize()
    
    # Create Z3 variables for each friend: meeting start time, end time, and their order in the itinerary.
    for f in friends:
        f["start"] = Int(f"{f['name']}_start")
        f["end"] = Int(f"{f['name']}_end")
        f["order"] = Int(f"{f['name']}_order")
        # Meeting must last at least the minimum duration.
        opt.add(f["end"] - f["start"] >= f["min_duration"])
        # Meeting must occur within the available window.
        opt.add(f["start"] >= f["avail_start"])
        opt.add(f["end"] <= f["avail_end"])
        # The order variable is in the range 0..n-1 (n = number of friends).
        opt.add(f["order"] >= 0, f["order"] < len(friends))
    
    # Ensure that each meeting gets a unique position in the itinerary.
    opt.add(Distinct([f["order"] for f in friends]))
    
    # You start your day at Presidio at 9:00 (540 minutes)
    start_time_presidio = 9 * 60
    
    # Constraint for the first meeting in the itinerary: your arrival at the friend's location
    # must account for the travel time from Presidio.
    for f in friends:
        travel_time = travel[("Presidio", f["location"])]
        opt.add(Implies(f["order"] == 0, f["start"] >= start_time_presidio + travel_time))
    
    # For any two meetings, if friend f is scheduled before friend g then ensure:
    # (f's end time) + (travel time between f.location and g.location) <= (g's start time)
    for f in friends:
        for g in friends:
            if f["name"] != g["name"]:
                travel_time_fg = travel[(f["location"], g["location"])]
                opt.add(Implies(f["order"] < g["order"], g["start"] >= f["end"] + travel_time_fg))
    
    # Introduce a finish_time variable representing the end time of your last meeting.
    # We will minimize this finish_time so that waiting times are reduced.
    finish_time = Int("finish_time")
    for f in friends:
        opt.add(finish_time >= f["end"])
    opt.minimize(finish_time)
    
    # Check and extract a solution.
    if opt.check() == sat:
        model = opt.model()
        # Collect the meetings with their computed times and order.
        schedule = []
        for f in friends:
            order_val = model.eval(f["order"]).as_long()
            start_val = model.eval(f["start"]).as_long()
            end_val = model.eval(f["end"]).as_long()
            schedule.append((order_val, {
                "action": "meet",
                "location": f["location"],
                "person": f["name"],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            }))
        # Sort meetings by their order in the itinerary.
        itinerary = [entry for _, entry in sorted(schedule, key=lambda x: x[0])]
        output = {"itinerary": itinerary}
        print(json.dumps(output))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()