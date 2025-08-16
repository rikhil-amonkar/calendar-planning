import json
from z3 import *

def hm(h, m):
    return h * 60 + m

def minutes_to_hhmm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Locations
locations = [
    "Richmond District",
    "Chinatown",
    "Sunset District",
    "Alamo Square",
    "Financial District",
    "North Beach",
    "Embarcadero",
    "Presidio",
    "Golden Gate Park",
    "Bayview",
]

# Travel times (minutes) as given
T = {}
def set_t(a, b, t):
    T[(a, b)] = t

set_t("Richmond District", "Chinatown", 20)
set_t("Richmond District", "Sunset District", 11)
set_t("Richmond District", "Alamo Square", 13)
set_t("Richmond District", "Financial District", 22)
set_t("Richmond District", "North Beach", 17)
set_t("Richmond District", "Embarcadero", 19)
set_t("Richmond District", "Presidio", 7)
set_t("Richmond District", "Golden Gate Park", 9)
set_t("Richmond District", "Bayview", 27)

set_t("Chinatown", "Richmond District", 20)
set_t("Chinatown", "Sunset District", 29)
set_t("Chinatown", "Alamo Square", 17)
set_t("Chinatown", "Financial District", 5)
set_t("Chinatown", "North Beach", 3)
set_t("Chinatown", "Embarcadero", 5)
set_t("Chinatown", "Presidio", 19)
set_t("Chinatown", "Golden Gate Park", 23)
set_t("Chinatown", "Bayview", 20)

set_t("Sunset District", "Richmond District", 12)
set_t("Sunset District", "Chinatown", 30)
set_t("Sunset District", "Alamo Square", 17)
set_t("Sunset District", "Financial District", 30)
set_t("Sunset District", "North Beach", 28)
set_t("Sunset District", "Embarcadero", 30)
set_t("Sunset District", "Presidio", 16)
set_t("Sunset District", "Golden Gate Park", 11)
set_t("Sunset District", "Bayview", 22)

set_t("Alamo Square", "Richmond District", 11)
set_t("Alamo Square", "Chinatown", 15)
set_t("Alamo Square", "Sunset District", 16)
set_t("Alamo Square", "Financial District", 17)
set_t("Alamo Square", "North Beach", 15)
set_t("Alamo Square", "Embarcadero", 16)
set_t("Alamo Square", "Presidio", 17)
set_t("Alamo Square", "Golden Gate Park", 9)
set_t("Alamo Square", "Bayview", 16)

set_t("Financial District", "Richmond District", 21)
set_t("Financial District", "Chinatown", 5)
set_t("Financial District", "Sunset District", 30)
set_t("Financial District", "Alamo Square", 17)
set_t("Financial District", "North Beach", 7)
set_t("Financial District", "Embarcadero", 4)
set_t("Financial District", "Presidio", 22)
set_t("Financial District", "Golden Gate Park", 23)
set_t("Financial District", "Bayview", 19)

set_t("North Beach", "Richmond District", 18)
set_t("North Beach", "Chinatown", 6)
set_t("North Beach", "Sunset District", 27)
set_t("North Beach", "Alamo Square", 16)
set_t("North Beach", "Financial District", 8)
set_t("North Beach", "Embarcadero", 6)
set_t("North Beach", "Presidio", 17)
set_t("North Beach", "Golden Gate Park", 22)
set_t("North Beach", "Bayview", 25)

set_t("Embarcadero", "Richmond District", 21)
set_t("Embarcadero", "Chinatown", 7)
set_t("Embarcadero", "Sunset District", 30)
set_t("Embarcadero", "Alamo Square", 19)
set_t("Embarcadero", "Financial District", 5)
set_t("Embarcadero", "North Beach", 5)
set_t("Embarcadero", "Presidio", 20)
set_t("Embarcadero", "Golden Gate Park", 25)
set_t("Embarcadero", "Bayview", 21)

set_t("Presidio", "Richmond District", 7)
set_t("Presidio", "Chinatown", 21)
set_t("Presidio", "Sunset District", 15)
set_t("Presidio", "Alamo Square", 19)
set_t("Presidio", "Financial District", 23)
set_t("Presidio", "North Beach", 18)
set_t("Presidio", "Embarcadero", 20)
set_t("Presidio", "Golden Gate Park", 12)
set_t("Presidio", "Bayview", 31)

set_t("Golden Gate Park", "Richmond District", 7)
set_t("Golden Gate Park", "Chinatown", 23)
set_t("Golden Gate Park", "Sunset District", 10)
set_t("Golden Gate Park", "Alamo Square", 9)
set_t("Golden Gate Park", "Financial District", 26)
set_t("Golden Gate Park", "North Beach", 23)
set_t("Golden Gate Park", "Embarcadero", 25)
set_t("Golden Gate Park", "Presidio", 11)
set_t("Golden Gate Park", "Bayview", 23)

set_t("Bayview", "Richmond District", 25)
set_t("Bayview", "Chinatown", 19)
set_t("Bayview", "Sunset District", 23)
set_t("Bayview", "Alamo Square", 16)
set_t("Bayview", "Financial District", 19)
set_t("Bayview", "North Beach", 22)
set_t("Bayview", "Embarcadero", 19)
set_t("Bayview", "Presidio", 32)
set_t("Bayview", "Golden Gate Park", 22)

# People data: location, availability window, required meeting duration
people = {
    "Robert":  {"loc": "Chinatown",          "win": (hm(7,45),  hm(17,30)), "dur": 120},
    "David":   {"loc": "Sunset District",     "win": (hm(12,30), hm(19,45)), "dur": 45},
    "Matthew": {"loc": "Alamo Square",       "win": (hm(8,45),  hm(13,45)), "dur": 90},
    "Jessica": {"loc": "Financial District", "win": (hm(9,30),  hm(18,45)), "dur": 45},
    "Melissa": {"loc": "North Beach",        "win": (hm(7,15),  hm(16,45)), "dur": 45},
    "Mark":    {"loc": "Embarcadero",        "win": (hm(15,15), hm(17,0)),  "dur": 45},
    "Deborah": {"loc": "Presidio",           "win": (hm(19,0),  hm(19,45)), "dur": 45},
    "Karen":   {"loc": "Golden Gate Park",   "win": (hm(19,30), hm(22,0)),  "dur": 120},
    "Laura":   {"loc": "Bayview",            "win": (hm(21,15), hm(22,15)), "dur": 15},
}

names = list(people.keys())
start_location = "Richmond District"
arrival_time = hm(9,0)

# Z3 Optimize model
opt = Optimize()

start_vars = {}
end_vars = {}
meet_vars = {}

# Create variables and constraints per person
for name in names:
    start = Int(f"start_{name}")
    end = Int(f"end_{name}")
    meet = Bool(f"meet_{name}")
    loc = people[name]["loc"]
    wstart, wend = people[name]["win"]
    dur = people[name]["dur"]

    start_vars[name] = start
    end_vars[name] = end
    meet_vars[name] = meet

    # Basic domains
    opt.add(start >= 0, end >= 0)
    # Duration fixed to minimum requirement
    opt.add(end == start + dur)
    # Availability window and initial travel feasibility from Richmond
    opt.add(Implies(meet, And(
        start >= wstart,
        end <= wend,
        start >= arrival_time + T[(start_location, loc)]
    )))

# Non-overlap + travel-time disjunction constraints for any pair selected
for i in range(len(names)):
    for j in range(i+1, len(names)):
        a = names[i]
        b = names[j]
        la = people[a]["loc"]
        lb = people[b]["loc"]
        # If both meetings are chosen, one must happen before the other with travel time
        opt.add(Implies(And(meet_vars[a], meet_vars[b]),
                        Or(end_vars[a] + T[(la, lb)] <= start_vars[b],
                           end_vars[b] + T[(lb, la)] <= start_vars[a])))

# Objective: maximize number of meetings
total_meetings = Sum([If(meet_vars[n], 1, 0) for n in names])
opt.maximize(total_meetings)

# Optional tie-breaker: minimize latest end time to prefer earlier finish among optimal counts
latest_end = Int("latest_end")
opt.add(latest_end == If(len(names) == 0, 0, Max([If(meet_vars[n], end_vars[n], 0) for n in names])))
opt.minimize(latest_end)

# Solve
if opt.check() != sat:
    print("SOLUTION:")
    print(json.dumps({"itinerary": []}))
else:
    model = opt.model()
    meetings = []
    for name in names:
        if is_true(model[meet_vars[name]]):
            s = model[start_vars[name]].as_long()
            e = model[end_vars[name]].as_long()
            meetings.append((s, e, name))
    # Sort by start time
    meetings.sort(key=lambda x: x[0])
    itinerary = []
    for s, e, name in meetings:
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_hhmm(s),
            "end_time": minutes_to_hhmm(e)
        })
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}))