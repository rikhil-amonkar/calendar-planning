from z3 import *
import json

def to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

travel_time = {
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Richmond District", "Bayview"): 26,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Richmond District"): 18
}

start_bayview = to_minutes("09:00")

meetings = {
    "Jason": {
        "location": "Fisherman's Wharf",
        "window_start": to_minutes("16:00"),
        "window_end": to_minutes("16:45"),
        "duration": 30
    },
    "Jessica": {
        "location": "Embarcadero",
        "window_start": to_minutes("16:45"),
        "window_end": to_minutes("19:00"),
        "duration": 30
    },
    "Sandra": {
        "location": "Richmond District",
        "window_start": to_minutes("18:30"),
        "window_end": to_minutes("21:45"),
        "duration": 120
    }
}

s = Solver()
start_jason = Int('start_jason')
start_jessica = Int('start_jessica')
start_sandra = Int('start_sandra')

s.add(start_jason >= meetings["Jason"]["window_start"])
s.add(start_jason + meetings["Jason"]["duration"] <= meetings["Jason"]["window_end"])

s.add(start_jessica >= meetings["Jessica"]["window_start"])
s.add(start_jessica + meetings["Jessica"]["duration"] <= meetings["Jessica"]["window_end"])

s.add(start_sandra >= meetings["Sandra"]["window_start"])
s.add(start_sandra + meetings["Sandra"]["duration"] <= meetings["Sandra"]["window_end"])

s.add(start_bayview + travel_time[("Bayview", meetings["Jason"]["location"])] <= start_jason)
s.add(start_jason + meetings["Jason"]["duration"] + travel_time[(meetings["Jason"]["location"], meetings["Jessica"]["location"])] <= start_jessica)
s.add(start_jessica + meetings["Jessica"]["duration"] + travel_time[(meetings["Jessica"]["location"], meetings["Sandra"]["location"])] <= start_sandra)

if s.check() == sat:
    model = s.model()
    jason_start = model.eval(start_jason).as_long()
    jessica_start = model.eval(start_jessica).as_long()
    sandra_start = model.eval(start_sandra).as_long()
    
    itinerary = [
        {"action": "meet", "person": "Jason", "start_time": to_time_str(jason_start), "end_time": to_time_str(jason_start + meetings["Jason"]["duration"])},
        {"action": "meet", "person": "Jessica", "start_time": to_time_str(jessica_start), "end_time": to_time_str(jessica_start + meetings["Jessica"]["duration"])},
        {"action": "meet", "person": "Sandra", "start_time": to_time_str(sandra_start), "end_time": to_time_str(sandra_start + meetings["Sandra"]["duration"])}
    ]
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}))
else:
    print("SOLUTION: No schedule found")