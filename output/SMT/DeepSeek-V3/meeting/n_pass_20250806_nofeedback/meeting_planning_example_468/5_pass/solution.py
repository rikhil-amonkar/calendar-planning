from z3 import *
import json

# Define travel times between locations (in minutes)
travel_times = {
    "The Castro": {
        "Bayview": 19,
        "Pacific Heights": 16,
        "Alamo Square": 8,
        "Fisherman's Wharf": 24,
        "Golden Gate Park": 11
    },
    "Bayview": {
        "The Castro": 20,
        "Pacific Heights": 23,
        "Alamo Square": 16,
        "Fisherman's Wharf": 25,
        "Golden Gate Park": 22
    },
    "Pacific Heights": {
        "The Castro": 16,
        "Bayview": 22,
        "Alamo Square": 10,
        "Fisherman's Wharf": 13,
        "Golden Gate Park": 15
    },
    "Alamo Square": {
        "The Castro": 8,
        "Bayview": 16,
        "Pacific Heights": 10,
        "Fisherman's Wharf": 19,
        "Golden Gate Park": 9
    },
    "Fisherman's Wharf": {
        "The Castro": 26,
        "Bayview": 26,
        "Pacific Heights": 12,
        "Alamo Square": 20,
        "Golden Gate Park": 25
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "Bayview": 23,
        "Pacific Heights": 16,
        "Alamo Square": 10,
        "Fisherman's Wharf": 24
    }
}

# Define friends and their availability
friends = {
    "Rebecca": {
        "location": "Bayview",
        "start": 9 * 60,  # 9:00 AM in minutes
        "end": 12 * 60 + 45  # 12:45 PM in minutes
    },
    "Amanda": {
        "location": "Pacific Heights",
        "start": 18 * 60 + 30,  # 6:30 PM in minutes
        "end": 21 * 60 + 45  # 9:45 PM in minutes
    },
    "James": {
        "location": "Alamo Square",
        "start": 9 * 60 + 45,  # 9:45 AM in minutes
        "end": 21 * 60 + 15  # 9:15 PM in minutes
    },
    "Sarah": {
        "location": "Fisherman's Wharf",
        "start": 8 * 60,  # 8:00 AM in minutes
        "end": 21 * 60 + 30  # 9:30 PM in minutes
    },
    "Melissa": {
        "location": "Golden Gate Park",
        "start": 9 * 60,  # 9:00 AM in minutes
        "end": 18 * 60 + 45  # 6:45 PM in minutes
    }
}

# Minimum meeting duration in minutes
min_duration = 90

# Initialize Z3 solver
s = Solver()

# Create variables for each meeting
meetings = {}
for friend in friends:
    meetings[friend] = {
        "start": Int(f"start_{friend}"),
        "end": Int(f"end_{friend}"),
        "met": Bool(f"met_{friend}"),
        "location": friends[friend]["location"]
    }

# Constraints for each meeting
for friend in friends:
    data = friends[friend]
    start_var = meetings[friend]["start"]
    end_var = meetings[friend]["end"]
    met_var = meetings[friend]["met"]
    
    # If meeting happens, it must be within availability window
    s.add(Implies(met_var, start_var >= data["start"]))
    s.add(Implies(met_var, end_var <= data["end"]))
    s.add(Implies(met_var, end_var == start_var + min_duration))
    
    # If not meeting, set times to 0
    s.add(Implies(Not(met_var), start_var == 0))
    s.add(Implies(Not(met_var), end_var == 0))

# Create order variables to sequence meetings
order = {}
friends_list = list(friends.keys())
for i in range(len(friends_list)):
    for j in range(i+1, len(friends_list)):
        f1 = friends_list[i]
        f2 = friends_list[j]
        order[(f1, f2)] = Bool(f"order_{f1}_{f2}")

# Sequencing constraints
for f1 in friends:
    for f2 in friends:
        if f1 != f2:
            s.add(Or(
                And(order.get((f1, f2), False), 
                    meetings[f1]["end"] + travel_times[meetings[f1]["location"]][meetings[f2]["location"]] <= meetings[f2]["start"]),
                And(order.get((f2, f1), False),
                    meetings[f2]["end"] + travel_times[meetings[f2]["location"]][meetings[f1]["location"]] <= meetings[f1]["start"]),
                Not(meetings[f1]["met"]),
                Not(meetings[f2]["met"])
            ))

# Starting point constraint
s.add(Or(
    *[And(meetings[friend]["met"], 
          meetings[friend]["start"] >= 9*60 + travel_times["The Castro"][meetings[friend]["location"]])
      for friend in friends],
    And([Not(meetings[friend]["met"]) for friend in friends])  # No meetings case
))

# Try to meet as many friends as possible
num_meetings = Sum([If(meetings[friend]["met"], 1, 0) for friend in friends])
s.maximize(num_meetings)

# Solve
if s.check() == sat:
    model = s.model()
    itinerary = []
    
    for friend in friends:
        if model.evaluate(meetings[friend]["met"]):
            start = model.evaluate(meetings[friend]["start"]).as_long()
            end = model.evaluate(meetings[friend]["end"]).as_long()
            
            start_hh = start // 60
            start_mm = start % 60
            end_hh = end // 60
            end_mm = end % 60
            
            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": f"{start_hh:02d}:{start_mm:02d}",
                "end_time": f"{end_hh:02d}:{end_mm:02d}",
                "location": meetings[friend]["location"]
            })
    
    itinerary.sort(key=lambda x: x["start_time"])
    
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print('No solution found')