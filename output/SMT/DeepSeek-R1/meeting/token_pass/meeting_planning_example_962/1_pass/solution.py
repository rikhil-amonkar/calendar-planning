import z3
import json

def time_to_minutes(time_str):
    time_str = time_str.replace(' ', '')
    if time_str.endswith('AM') or time_str.endswith('PM'):
        parts = time_str[:-2].split(':')
        hour = int(parts[0])
        minute = int(parts[1]) if len(parts) > 1 else 0
        if time_str.endswith('PM') and hour != 12:
            hour += 12
        elif time_str.endswith('AM') and hour == 12:
            hour = 0
        return hour * 60 + minute
    else:
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1]) if len(parts) > 1 else 0
        return hour * 60 + minute

def minutes_to_time(minutes):
    total_minutes = int(minutes)
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    "The Castro": {
        "Marina District": 21,
        "Presidio": 20,
        "North Beach": 20,
        "Embarcadero": 22,
        "Haight-Ashbury": 6,
        "Golden Gate Park": 11,
        "Richmond District": 16,
        "Alamo Square": 8,
        "Financial District": 21,
        "Sunset District": 17
    },
    "Marina District": {
        "The Castro": 22,
        "Presidio": 10,
        "North Beach": 11,
        "Embarcadero": 14,
        "Haight-Ashbury": 16,
        "Golden Gate Park": 18,
        "Richmond District": 11,
        "Alamo Square": 15,
        "Financial District": 17,
        "Sunset District": 19
    },
    "Presidio": {
        "The Castro": 21,
        "Marina District": 11,
        "North Beach": 18,
        "Embarcadero": 20,
        "Haight-Ashbury": 15,
        "Golden Gate Park": 12,
        "Richmond District": 7,
        "Alamo Square": 19,
        "Financial District": 23,
        "Sunset District": 15
    },
    "North Beach": {
        "The Castro": 23,
        "Marina District": 9,
        "Presidio": 17,
        "Embarcadero": 6,
        "Haight-Ashbury": 18,
        "Golden Gate Park": 22,
        "Richmond District": 18,
        "Alamo Square": 16,
        "Financial District": 8,
        "Sunset District": 27
    },
    "Embarcadero": {
        "The Castro": 25,
        "Marina District": 12,
        "Presidio": 20,
        "North Beach": 5,
        "Haight-Ashbury": 21,
        "Golden Gate Park": 25,
        "Richmond District": 21,
        "Alamo Square": 19,
        "Financial District": 5,
        "Sunset District": 30
    },
    "Haight-Ashbury": {
        "The Castro": 6,
        "Marina District": 17,
        "Presidio": 15,
        "North Beach": 19,
        "Embarcadero": 20,
        "Golden Gate Park": 7,
        "Richmond District": 10,
        "Alamo Square": 5,
        "Financial District": 21,
        "Sunset District": 15
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "Marina District": 16,
        "Presidio": 11,
        "North Beach": 23,
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Richmond District": 7,
        "Alamo Square": 9,
        "Financial District": 26,
        "Sunset District": 10
    },
    "Richmond District": {
        "The Castro": 16,
        "Marina District": 9,
        "Presidio": 7,
        "North Beach": 17,
        "Embarcadero": 19,
        "Haight-Ashbury": 10,
        "Golden Gate Park": 9,
        "Alamo Square": 13,
        "Financial District": 22,
        "Sunset District": 11
    },
    "Alamo Square": {
        "The Castro": 8,
        "Marina District": 15,
        "Presidio": 17,
        "North Beach": 15,
        "Embarcadero": 16,
        "Haight-Ashbury": 5,
        "Golden Gate Park": 9,
        "Richmond District": 11,
        "Financial District": 17,
        "Sunset District": 16
    },
    "Financial District": {
        "The Castro": 20,
        "Marina District": 15,
        "Presidio": 22,
        "North Beach": 7,
        "Embarcadero": 4,
        "Haight-Ashbury": 19,
        "Golden Gate Park": 23,
        "Richmond District": 21,
        "Alamo Square": 17,
        "Sunset District": 30
    },
    "Sunset District": {
        "The Castro": 17,
        "Marina District": 21,
        "Presidio": 16,
        "North Beach": 28,
        "Embarcadero": 30,
        "Haight-Ashbury": 15,
        "Golden Gate Park": 11,
        "Richmond District": 12,
        "Alamo Square": 17,
        "Financial District": 30
    }
}

friends = [
    {"name": "Elizabeth", "location": "Marina District", "available_start": "19:00", "available_end": "20:45", "min_duration": 105},
    {"name": "Joshua", "location": "Presidio", "available_start": "8:30AM", "available_end": "13:15", "min_duration": 105},
    {"name": "Timothy", "location": "North Beach", "available_start": "19:45", "available_end": "22:00", "min_duration": 90},
    {"name": "David", "location": "Embarcadero", "available_start": "10:45", "available_end": "12:30", "min_duration": 30},
    {"name": "Kimberly", "location": "Haight-Ashbury", "available_start": "16:45", "available_end": "21:30", "min_duration": 75},
    {"name": "Lisa", "location": "Golden Gate Park", "available_start": "17:30", "available_end": "21:45", "min_duration": 45},
    {"name": "Ronald", "location": "Richmond District", "available_start": "8:00AM", "available_end": "9:30", "min_duration": 90},
    {"name": "Stephanie", "location": "Alamo Square", "available_start": "15:30", "available_end": "16:30", "min_duration": 30},
    {"name": "Helen", "location": "Financial District", "available_start": "17:30", "available_end": "18:30", "min_duration": 45},
    {"name": "Laura", "location": "Sunset District", "available_start": "17:45", "available_end": "21:15", "min_duration": 90}
]

base_time = time_to_minutes("9:00AM")
meetings = []
for friend in friends:
    start_time = time_to_minutes(friend["available_start"]) - base_time
    end_time = time_to_minutes(friend["available_end"]) - base_time
    meetings.append({
        "name": friend["name"],
        "location": friend["location"],
        "start_avail": start_time,
        "end_avail": end_time,
        "min_duration": friend["min_duration"]
    })

n = len(meetings)
solver = z3.Optimize()
starts = [z3.Real(f"start_{i}") for i in range(n)]
ends = [z3.Real(f"end_{i}") for i in range(n)]
scheduled = [z3.Bool(f"scheduled_{i}") for i in range(n)]

for i in range(n):
    m = meetings[i]
    solver.add(z3.Implies(scheduled[i], starts[i] >= m["start_avail"]))
    solver.add(z3.Implies(scheduled[i], ends[i] <= m["end_avail"]))
    solver.add(z3.Implies(scheduled[i], ends[i] == starts[i] + m["min_duration"]))
    solver.add(z3.Implies(scheduled[i], starts[i] >= travel_times["The Castro"][m["location"]]))

for i in range(n):
    for j in range(i+1, n):
        if i != j:
            constraint = z3.Or(
                ends[i] + travel_times[meetings[i]["location"]][meetings[j]["location"]] <= starts[j],
                ends[j] + travel_times[meetings[j]["location"]][meetings[i]["location"]] <= starts[i]
            )
            solver.add(z3.Implies(z3.And(scheduled[i], scheduled[j]), constraint))

solver.maximize(z3.Sum([z3.If(scheduled[i], 1, 0) for i in range(n)]))

if solver.check() == z3.sat:
    model = solver.model()
    itinerary = []
    for i in range(n):
        if z3.is_true(model.eval(scheduled[i])):
            start_val = model.eval(starts[i])
            end_val = model.eval(ends[i])
            if isinstance(start_val, z3.RatNumRef) and isinstance(end_val, z3.RatNumRef):
                start_minutes = start_val.as_long()
                end_minutes = end_val.as_long()
                start_time_actual = base_time + start_minutes
                end_time_actual = base_time + end_minutes
                itinerary.append({
                    "action": "meet",
                    "location": meetings[i]["location"],
                    "person": meetings[i]["name"],
                    "start_time": minutes_to_time(start_time_actual),
                    "end_time": minutes_to_time(end_time_actual)
                })
    itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print('{"itinerary": []}')