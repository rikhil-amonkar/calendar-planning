from z3 import *
import json

# Define travel times between locations
travel_times = {
    ("Chinatown", "Mission District"): 18,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Presidio"): 19,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Presidio"): 25,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Presidio"): 18,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Presidio"): 11,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Presidio"): 24,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Presidio"): 11,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Presidio"): 16,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Sunset District"): 15,
}

# Define friends and their availability
friends = [
    {"name": "David", "location": "Mission District", "available_start": 8*60, "available_end": 19*60+45, "duration": 45},
    {"name": "Kenneth", "location": "Alamo Square", "available_start": 14*60, "available_end": 19*60+45, "duration": 120},
    {"name": "John", "location": "Pacific Heights", "available_start": 17*60, "available_end": 20*60, "duration": 15},
    {"name": "Charles", "location": "Union Square", "available_start": 21*60+45, "available_end": 22*60+45, "duration": 60},
    {"name": "Deborah", "location": "Golden Gate Park", "available_start": 7*60, "available_end": 18*60+15, "duration": 90},
    {"name": "Karen", "location": "Sunset District", "available_start": 17*60+45, "available_end": 21*60+15, "duration": 15},
    {"name": "Carol", "location": "Presidio", "available_start": 8*60+15, "available_end": 9*60+15, "duration": 30},
]

# Initialize Z3 solver
s = Optimize()

# Create variables for each meeting
meetings = []
for friend in friends:
    start = Int(f"start_{friend['name']}")
    end = Int(f"end_{friend['name']}")
    meetings.append({
        "name": friend["name"],
        "location": friend["location"],
        "start": start,
        "end": end,
        "duration": friend["duration"],
        "available_start": friend["available_start"],
        "available_end": friend["available_end"],
    })

# Add basic constraints
for meeting in meetings:
    s.add(meeting["start"] >= meeting["available_start"])
    s.add(meeting["end"] <= meeting["available_end"])
    s.add(meeting["end"] == meeting["start"] + meeting["duration"])

# Define meeting sequence and travel constraints
current_location = "Chinatown"
current_time = 9 * 60  # 9:00 AM

# We'll try to meet Carol first since she's only available in the morning
carol = next(m for m in meetings if m["name"] == "Carol")
s.add(carol["start"] >= current_time + travel_times[(current_location, carol["location"])])

# Then meet David
david = next(m for m in meetings if m["name"] == "David")
s.add(david["start"] >= carol["end"] + travel_times[(carol["location"], david["location"])])

# Then meet Deborah
deborah = next(m for m in meetings if m["name"] == "Deborah")
s.add(deborah["start"] >= david["end"] + travel_times[(david["location"], deborah["location"])])

# Then meet Kenneth
kenneth = next(m for m in meetings if m["name"] == "Kenneth")
s.add(kenneth["start"] >= deborah["end"] + travel_times[(deborah["location"], kenneth["location"])])

# Then meet John
john = next(m for m in meetings if m["name"] == "John")
s.add(john["start"] >= kenneth["end"] + travel_times[(kenneth["location"], john["location"])])

# Then meet Karen
karen = next(m for m in meetings if m["name"] == "Karen")
s.add(karen["start"] >= john["end"] + travel_times[(john["location"], karen["location"])])

# Finally meet Charles
charles = next(m for m in meetings if m["name"] == "Charles")
s.add(charles["start"] >= karen["end"] + travel_times[(karen["location"], charles["location"])])

# Try to maximize the number of meetings
s.maximize(charles["start"])

if s.check() == sat:
    model = s.model()
    itinerary = []
    for meeting in meetings:
        start_time = model.eval(meeting["start"]).as_long()
        end_time = model.eval(meeting["end"]).as_long()
        itinerary.append({
            "action": "meet",
            "person": meeting["name"],
            "start_time": f"{start_time//60:02d}:{start_time%60:02d}",
            "end_time": f"{end_time//60:02d}:{end_time%60:02d}",
        })
    itinerary.sort(key=lambda x: x["start_time"])
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No valid schedule found that meets all constraints")