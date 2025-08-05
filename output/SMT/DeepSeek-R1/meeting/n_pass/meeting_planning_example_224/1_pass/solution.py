from z3 import *
import json

# Travel times dictionary
travel_times = {
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Richmond District"): 7,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Presidio"): 7
}

# Meetings: index 0: Melissa, 1: Emily, 2: Nancy
meetings = [
    {
        "name": "Melissa",
        "location": "Golden Gate Park",
        "min_duration": 15,
        "available_start": 8*60+30,  # 8:30 AM = 510 minutes
        "available_end": 20*60       # 8:00 PM = 1200 minutes
    },
    {
        "name": "Emily",
        "location": "Richmond District",
        "min_duration": 120,
        "available_start": 16*60+45, # 4:45 PM = 1005 minutes
        "available_end": 22*60       # 10:00 PM = 1320 minutes
    },
    {
        "name": "Nancy",
        "location": "Presidio",
        "min_duration": 105,
        "available_start": 19*60+45, # 7:45 PM = 1185 minutes
        "available_end": 22*60       # 10:00 PM = 1320 minutes
    }
]

# Start at Fisherman's Wharf at 9:00 AM = 540 minutes
start_time = 540
start_loc = "Fisherman's Wharf"

s = Solver()

# Define the order: first, second, third as integers in [0,1,2]
first = Int('first')
second = Int('second')
third = Int('third')

s.add(And(first >= 0, first <= 2))
s.add(And(second >= 0, second <= 2))
s.add(And(third >= 0, third <= 2))
s.add(Distinct(first, second, third))

# We'll define the start times for the first, second, third meeting
s_first = Int('s_first')
s_second = Int('s_second')
s_third = Int('s_third')

# Define end times
e_first = Int('e_first')
e_second = Int('e_second')
e_third = Int('e_third')

# Define travel times for the segments
travel0 = Int('travel0')
travel1 = Int('travel1')
travel2 = Int('travel2')

# Define travel0: from start_loc to the first meeting's location
s.add(travel0 == If(first == 0, 
                travel_times[(start_loc, meetings[0]["location"])],
                If(first == 1,
                travel_times[(start_loc, meetings[1]["location"])],
                travel_times[(start_loc, meetings[2]["location"])]
                )))

# Define travel1: from first meeting's location to second meeting's location
s.add(travel1 == If(And(first == 0, second == 1),
                travel_times[(meetings[0]["location"], meetings[1]["location"])],
                If(And(first == 0, second == 2),
                travel_times[(meetings[0]["location"], meetings[2]["location"])],
                If(And(first == 1, second == 0),
                travel_times[(meetings[1]["location"], meetings[0]["location"])],
                If(And(first == 1, second == 2),
                travel_times[(meetings[1]["location"], meetings[2]["location"])],
                If(And(first == 2, second == 0),
                travel_times[(meetings[2]["location"], meetings[0]["location"])],
                If(And(first == 2, second == 1),
                travel_times[(meetings[2]["location"], meetings[1]["location"])],
                0)))))))

# Define travel2: from second meeting's location to third meeting's location
s.add(travel2 == If(And(second == 0, third == 1),
                travel_times[(meetings[0]["location"], meetings[1]["location"])],
                If(And(second == 0, third == 2),
                travel_times[(meetings[0]["location"], meetings[2]["location"])],
                If(And(second == 1, third == 0),
                travel_times[(meetings[1]["location"], meetings[0]["location"])],
                If(And(second == 1, third == 2),
                travel_times[(meetings[1]["location"], meetings[2]["location"])],
                If(And(second == 2, third == 0),
                travel_times[(meetings[2]["location"], meetings[0]["location"])],
                If(And(second == 2, third == 1),
                travel_times[(meetings[2]["location"], meetings[1]["location"])],
                0)))))))

# Constraints for the first meeting
s.add(s_first >= start_time + travel0)
s.add(e_first == s_first + 
      If(first == 0, meetings[0]["min_duration"],
        If(first == 1, meetings[1]["min_duration"], meetings[2]["min_duration"])))

# Constraints for the second meeting
s.add(s_second >= e_first + travel1)
s.add(e_second == s_second + 
      If(second == 0, meetings[0]["min_duration"],
        If(second == 1, meetings[1]["min_duration"], meetings[2]["min_duration"])))

# Constraints for the third meeting
s.add(s_third >= e_second + travel2)
s.add(e_third == s_third + 
      If(third == 0, meetings[0]["min_duration"],
        If(third == 1, meetings[1]["min_duration"], meetings[2]["min_duration"])))

# Define the actual start time for each meeting (by index)
s0 = Int('s0')   # start time for Melissa (index0)
s1 = Int('s1')   # for Emily (index1)
s2 = Int('s2')   # for Nancy (index2)

s.add(s0 == If(first == 0, s_first, If(second == 0, s_second, s_third)))
s.add(s1 == If(first == 1, s_first, If(second == 1, s_second, s_third)))
s.add(s2 == If(first == 2, s_first, If(second == 2, s_second, s_third)))

# Constraints for each meeting: within available times and duration
# Melissa (index0)
s.add(s0 >= meetings[0]["available_start"])
s.add(s0 + meetings[0]["min_duration"] <= meetings[0]["available_end"])
# Emily (index1)
s.add(s1 >= meetings[1]["available_start"])
s.add(s1 + meetings[1]["min_duration"] <= meetings[1]["available_end"])
# Nancy (index2)
s.add(s2 >= meetings[2]["available_start"])
s.add(s2 + meetings[2]["min_duration"] <= meetings[2]["available_end"])

# Check if satisfiable
if s.check() == sat:
    m = s.model()
    # Get the start times for each meeting
    s0_val = m.evaluate(s0).as_long()
    s1_val = m.evaluate(s1).as_long()
    s2_val = m.evaluate(s2).as_long()

    # Convert to HH:MM
    def to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # Create the itinerary list
    itinerary = []
    # For Melissa
    itinerary.append({
        "action": "meet",
        "person": "Melissa",
        "start_time": to_time(s0_val),
        "end_time": to_time(s0_val + meetings[0]["min_duration"])
    })
    # For Emily
    itinerary.append({
        "action": "meet",
        "person": "Emily",
        "start_time": to_time(s1_val),
        "end_time": to_time(s1_val + meetings[1]["min_duration"])
    })
    # For Nancy
    itinerary.append({
        "action": "meet",
        "person": "Nancy",
        "start_time": to_time(s2_val),
        "end_time": to_time(s2_val + meetings[2]["min_duration"])
    })

    # Sort the itinerary by start_time
    itinerary_sorted = sorted(itinerary, key=lambda x: x['start_time'])
    result = {"itinerary": itinerary_sorted}
    print("SOLUTION: " + json.dumps(result))
else:
    print("SOLUTION: No valid schedule found")