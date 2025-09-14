#!/usr/bin/env python3
from z3 import Int, Bool, Optimize, If, And, Or, Not, Implies, sat, Sum
import json

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def main():
    travel_times = {
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "North Beach"): 7,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "North Beach"): 24,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "North Beach"): 3,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "North Beach"): 10,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "North Beach"): 9,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Pacific Heights"): 8,
    }
    
    friends = [
        { "name": "Stephanie", "location": "Golden Gate Park", "avail_start": 660, "avail_end": 900, "min_meet": 105 },
        { "name": "Karen",     "location": "Chinatown",        "avail_start": 825, "avail_end": 990, "min_meet": 15  },
        { "name": "Brian",     "location": "Union Square",     "avail_start": 900, "avail_end": 1035, "min_meet": 30 },
        { "name": "Rebecca",   "location": "Fisherman's Wharf","avail_start": 480, "avail_end": 675, "min_meet": 30 },
        { "name": "Joseph",    "location": "Pacific Heights",  "avail_start": 495, "avail_end": 570, "min_meet": 60 },
        { "name": "Steven",    "location": "North Beach",      "avail_start": 870, "avail_end": 1245, "min_meet": 120 },
    ]
    
    n = len(friends)
    opt = Optimize()
    
    r = [ Bool(f"r_{i}") for i in range(n) ]
    s = [ Int(f"s_{i}") for i in range(n) ]
    e = [ Int(f"e_{i}") for i in range(n) ]
    
    for i, friend in enumerate(friends):
        opt.add( Implies(r[i], s[i] >= friend["avail_start"]) )
        opt.add( Implies(r[i], s[i] >= 540 + travel_times[("Financial District", friend["location"])]) )
        opt.add( Implies(r[i], e[i] <= friend["avail_end"]) )
        opt.add( Implies(r[i], e[i] - s[i] >= friend["min_meet"]) )
        opt.add( Implies(r[i], s[i] >= 0) )
        opt.add( Implies(r[i], e[i] <= 1440) )
    
    for i in range(n):
        for j in range(i + 1, n):
            opt.add( Implies( And(r[i], r[j]),
                Or(
                    e[i] + travel_times[(friends[i]["location"], friends[j]["location"])] <= s[j],
                    e[j] + travel_times[(friends[j]["location"], friends[i]["location"])] <= s[i]
                )
            ))
    
    total_meetings = Sum([ If(r[i], 1, 0) for i in range(n) ])
    opt.maximize(total_meetings)
    
    if opt.check() == sat:
        model = opt.model()
        schedule = []
        for i, friend in enumerate(friends):
            if model.evaluate(r[i]):
                start_time = model.evaluate(s[i]).as_long()
                end_time = model.evaluate(e[i]).as_long()
                schedule.append({
                    "person": friend["name"],
                    "location": friend["location"],
                    "start": start_time,
                    "end": end_time
                })
        schedule.sort(key=lambda x: x["start"])
        
        itinerary = []
        for item in schedule:
            itinerary.append({
                "action": "meet",
                "location": item["location"],
                "person": item["person"],
                "start_time": format_time(item["start"]),
                "end_time": format_time(item["end"])
            })
        
        output = { "itinerary": itinerary }
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()