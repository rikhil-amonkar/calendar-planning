from z3 import *
import json

def minutes_to_time(m):
    h = m // 60
    m_rem = m % 60
    return f"{h}:{m_rem:02d}"

# Travel times dictionary (in minutes)
travel_times = {
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Marina District"): 12,
    
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Marina District"): 27,
    
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Marina District"): 12,
    
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Marina District"): 15,
    
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Marina District"): 11,
    
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Marina District"): 11,
    
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Marina District"): 18,
    
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Marina District"): 21,
    
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Marina District"): 9,
    
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Marina District"): 9,
    
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Fisherman's Wharf"): 10,
}

# Meeting constraints data
# Times are expressed in minutes from midnight.
# You arrive at Embarcadero at 9:00 -> 540
meetings_data = [
    {"person": "Matthew",   "location": "Bayview",           "avail_start": 1155, "avail_end": 1320, "min_duration": 120},
    {"person": "Karen",     "location": "Chinatown",         "avail_start": 1155, "avail_end": 1275, "min_duration": 90},
    {"person": "Sarah",     "location": "Alamo Square",      "avail_start": 1200, "avail_end": 1305, "min_duration": 105},
    {"person": "Jessica",   "location": "Nob Hill",          "avail_start": 990,  "avail_end": 1125, "min_duration": 120},
    {"person": "Stephanie", "location": "Presidio",          "avail_start": 450,  "avail_end": 615,  "min_duration": 60},
    {"person": "Mary",      "location": "Union Square",      "avail_start": 1005, "avail_end": 1290, "min_duration": 60},
    {"person": "Charles",   "location": "The Castro",        "avail_start": 990,  "avail_end": 1320, "min_duration": 105},
    {"person": "Nancy",     "location": "North Beach",       "avail_start": 885,  "avail_end": 1200, "min_duration": 15},
    {"person": "Thomas",    "location": "Fisherman's Wharf", "avail_start": 810,  "avail_end": 1140, "min_duration": 30},
    {"person": "Brian",     "location": "Marina District",   "avail_start": 735,  "avail_end": 1080, "min_duration": 60},
]

# Create an Optimize instance
opt = Optimize()

n = len(meetings_data)
# Decision variables for each meeting:
# scheduled[i]: whether meeting i is scheduled.
# start_vars[i], end_vars[i]: the meeting time window.
# order_vars[i]: the position (order) of meeting i if scheduled; if not scheduled, set to -1.
scheduled = [Bool(f"scheduled_{i}") for i in range(n)]
start_vars = [Int(f"start_{i}") for i in range(n)]
end_vars = [Int(f"end_{i}") for i in range(n)]
order_vars = [Int(f"order_{i}") for i in range(n)]

# Domain constraints for start and end times.
for i in range(n):
    opt.add(start_vars[i] >= 0, start_vars[i] <= 1440)
    opt.add(end_vars[i] >= 0, end_vars[i] <= 1440)

# If a meeting is not scheduled, force its order to be -1.
for i in range(n):
    opt.add(Implies(Not(scheduled[i]), order_vars[i] == -1))
    # If scheduled, order must be between 0 and n-1.
    opt.add(Implies(scheduled[i], And(order_vars[i] >= 0, order_vars[i] < n)))

# Meeting availability and duration constraints.
for i, m in enumerate(meetings_data):
    opt.add(Implies(scheduled[i], start_vars[i] >= m["avail_start"]))
    opt.add(Implies(scheduled[i], end_vars[i] <= m["avail_end"]))
    opt.add(Implies(scheduled[i], end_vars[i] - start_vars[i] >= m["min_duration"]))
    opt.add(Implies(scheduled[i], start_vars[i] < end_vars[i]))

# For the meeting that is first in the schedule (order == 0), ensure it is reachable from Embarcadero.
for i, m in enumerate(meetings_data):
    if ("Embarcadero", m["location"]) in travel_times:
        travel_from_E = travel_times[("Embarcadero", m["location"])]
    else:
        travel_from_E = 9999  # Fallback large value if missing.
    opt.add(Implies(And(scheduled[i], order_vars[i] == 0), start_vars[i] >= 540 + travel_from_E))

# Pairwise ordering and travel constraints:
# For any two scheduled meetings, they must have distinct orders.
# Also, if meeting i is scheduled before meeting j, then
# end_time(i) + travel_time(i->j) <= start_time(j).
for i in range(n):
    for j in range(i+1, n):
        # Enforce distinct order if both are scheduled.
        opt.add(Implies(And(scheduled[i], scheduled[j]), order_vars[i] != order_vars[j]))
        
        # Determine travel time from meeting i's location to j's location.
        mi = meetings_data[i]
        mj = meetings_data[j]
        travel_ij = travel_times.get((mi["location"], mj["location"]), 9999)
        travel_ji = travel_times.get((mj["location"], mi["location"]), 9999)
        
        opt.add(Implies(And(scheduled[i], scheduled[j], order_vars[i] < order_vars[j]),
                         end_vars[i] + travel_ij <= start_vars[j]))
        opt.add(Implies(And(scheduled[i], scheduled[j], order_vars[i] > order_vars[j]),
                         end_vars[j] + travel_ji <= start_vars[i]))

# Force that if any meeting is scheduled, at least one of them must be the first (order == 0).
first_meeting_exists = [And(scheduled[i], order_vars[i] == 0) for i in range(n)]
# If at least one meeting is scheduled, then one must have order 0.
opt.add(Or(Not(Or([scheduled[i] for i in range(n)])), Or(first_meeting_exists)))

# Objective: maximize the total number of meetings scheduled.
total_meetings = Sum([If(scheduled[i], 1, 0) for i in range(n)])
opt.maximize(total_meetings)

if opt.check() == sat:
    model = opt.model()
    scheduled_meetings = []
    for i in range(n):
        if is_true(model.evaluate(scheduled[i])):
            order_val = model.evaluate(order_vars[i]).as_long()
            start_val = model.evaluate(start_vars[i]).as_long()
            end_val = model.evaluate(end_vars[i]).as_long()
            scheduled_meetings.append((order_val, i, start_val, end_val))
    # Sort the scheduled meetings by their order in the itinerary.
    scheduled_meetings.sort(key=lambda x: x[0])
    itinerary = []
    for order_val, i, start_val, end_val in scheduled_meetings:
        meeting = meetings_data[i]
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time(start_val),
            "end_time": minutes_to_time(end_val)
        })
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print(json.dumps({"itinerary": []}))