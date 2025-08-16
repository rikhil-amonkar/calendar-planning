from z3 import Int, Optimize, And, Or, Implies
import json

def to_min(h, m):
    return h * 60 + m

def fmt_time(minutes):
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

# Problem data
arrival_location = "Alamo Square"
arrival_time = to_min(9, 0)  # 09:00

travel_time = {
    ("Alamo Square", "Richmond District"): 12,
    ("Richmond District", "Alamo Square"): 13
}

friends = [
    {
        "name": "Timothy",
        "location": "Richmond District",
        "avail_start": to_min(20, 45),  # 20:45
        "avail_end": to_min(21, 30),    # 21:30
        "min_duration": 45
    }
]

opt = Optimize()

# Variables
s_vars = {}
e_vars = {}
meet_vars = {}

for f in friends:
    name = f["name"]
    s = Int(f"s_{name}")
    e = Int(f"e_{name}")
    meet = Int(f"meet_{name}")  # 0/1
    
    s_vars[name] = s
    e_vars[name] = e
    meet_vars[name] = meet
    
    # Variable domains
    opt.add(s >= 0, s <= 1440, e >= 0, e <= 1440, meet >= 0, meet <= 1)
    
    # If meeting occurs, it must respect availability and min duration
    opt.add(Implies(
        meet == 1,
        And(
            s >= f["avail_start"],
            e <= f["avail_end"],
            e - s >= f["min_duration"],
            e > s
        )
    ))
    
    # Ensure feasibility from starting location considering travel time
    # You can wait at Alamo Square and depart at any time >= arrival_time.
    # If meeting happens at location L, s must be at least arrival_time + travel(Alamo, L).
    ttime = travel_time.get((arrival_location, f["location"]), None)
    if ttime is not None:
        opt.add(Implies(meet == 1, s >= arrival_time + ttime))
    else:
        # If no travel time known, disallow meeting (safety)
        opt.add(meet == 0)

# Objective: maximize number of meetings
opt.maximize(sum(meet_vars.values()))

# Solve
result = opt.check()
itinerary = []

if str(result) == "sat":
    model = opt.model()
    # Build itinerary for meetings that are scheduled
    for f in friends:
        name = f["name"]
        if model.eval(meet_vars[name]).as_long() == 1:
            s_val = model.eval(s_vars[name]).as_long()
            e_val = model.eval(e_vars[name]).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": fmt_time(s_val),
                "end_time": fmt_time(e_val)
            })

# Sort itinerary by start time
itinerary.sort(key=lambda x: x["start_time"])

# Output JSON
print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))