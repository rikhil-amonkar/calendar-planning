from z3 import *
import json

# Define travel_times dictionary
travel_times = {
    "Union Square": {
        "Mission District": 14,
        "Fisherman's Wharf": 15,
        "Russian Hill": 13,
        "Marina District": 18,
        "North Beach": 10,
        "Chinatown": 7,
        "Pacific Heights": 15,
        "The Castro": 17,
        "Nob Hill": 9,
        "Sunset District": 27
    },
    "Mission District": {
        "Union Square": 15,
        "Fisherman's Wharf": 22,
        "Russian Hill": 15,
        "Marina District": 19,
        "North Beach": 17,
        "Chinatown": 16,
        "Pacific Heights": 16,
        "The Castro": 7,
        "Nob Hill": 12,
        "Sunset District": 24
    },
    "Fisherman's Wharf": {
        "Union Square": 13,
        "Mission District": 22,
        "Russian Hill": 7,
        "Marina District": 9,
        "North Beach": 6,
        "Chinatown": 12,
        "Pacific Heights": 12,
        "The Castro": 27,
        "Nob Hill": 11,
        "Sunset District": 27
    },
    "Russian Hill": {
        "Union Square": 10,
        "Mission District": 16,
        "Fisherman's Wharf": 7,
        "Marina District": 7,
        "North Beach": 5,
        "Chinatown": 9,
        "Pacific Heights": 7,
        "The Castro": 21,
        "Nob Hill": 5,
        "Sunset District": 23
    },
    "Marina District": {
        "Union Square": 16,
        "Mission District": 20,
        "Fisherman's Wharf": 10,
        "Russian Hill": 8,
        "North Beach": 11,
        "Chinatown": 15,
        "Pacific Heights": 7,
        "The Castro": 22,
        "Nob Hill": 12,
        "Sunset District": 19
    },
    "North Beach": {
        "Union Square": 7,
        "Mission District": 18,
        "Fisherman's Wharf": 5,
        "Russian Hill": 4,
        "Marina District": 9,
        "Chinatown": 6,
        "Pacific Heights": 8,
        "The Castro": 23,
        "Nob Hill": 7,
        "Sunset District": 27
    },
    "Chinatown": {
        "Union Square": 7,
        "Mission District": 17,
        "Fisherman's Wharf": 8,
        "Russian Hill": 7,
        "Marina District": 12,
        "North Beach": 3,
        "Pacific Heights": 10,
        "The Castro": 22,
        "Nob Hill": 9,
        "Sunset District": 29
    },
    "Pacific Heights": {
        "Union Square": 12,
        "Mission District": 15,
        "Fisherman's Wharf": 13,
        "Russian Hill": 7,
        "Marina District": 6,
        "North Beach": 9,
        "Chinatown": 11,
        "The Castro": 16,
        "Nob Hill": 8,
        "Sunset District": 21
    },
    "The Castro": {
        "Union Square": 19,
        "Mission District": 7,
        "Fisherman's Wharf": 24,
        "Russian Hill": 18,
        "Marina District": 21,
        "North Beach": 20,
        "Chinatown": 22,
        "Pacific Heights": 16,
        "Nob Hill": 16,
        "Sunset District": 17
    },
    "Nob Hill": {
        "Union Square": 7,
        "Mission District": 13,
        "Fisherman's Wharf": 10,
        "Russian Hill": 5,
        "Marina District": 11,
        "North Beach": 8,
        "Chinatown": 6,
        "Pacific Heights": 8,
        "The Castro": 17,
        "Sunset District": 24
    },
    "Sunset District": {
        "Union Square": 30,
        "Mission District": 25,
        "Fisherman's Wharf": 29,
        "Russian Hill": 24,
        "Marina District": 21,
        "North Beach": 28,
        "Chinatown": 30,
        "Pacific Heights": 21,
        "The Castro": 17,
        "Nob Hill": 27
    }
}

# Define meetings: index 0 is the start event (Union Square at 9:00AM)
# For others: name, location, available_start (minutes from 9:00AM), available_end (minutes from 9:00AM), min_dur (minutes)
meetings = [
    {"name": "start", "loc": "Union Square", "avail_start": 0, "avail_end": 0, "min_dur": 0},
    {"name": "Kevin", "loc": "Mission District", "avail_start": 705, "avail_end": 765, "min_dur": 60},
    {"name": "Mark", "loc": "Fisherman's Wharf", "avail_start": 495, "avail_end": 660, "min_dur": 90},
    {"name": "Jessica", "loc": "Russian Hill", "avail_start": 0, "avail_end": 360, "min_dur": 120},
    {"name": "Jason", "loc": "Marina District", "avail_start": 375, "avail_end": 765, "min_dur": 120},
    {"name": "John", "loc": "North Beach", "avail_start": 45, "avail_end": 540, "min_dur": 15},
    {"name": "Karen", "loc": "Chinatown", "avail_start": 465, "avail_end": 600, "min_dur": 75},
    {"name": "Sarah", "loc": "Pacific Heights", "avail_start": 510, "avail_end": 555, "min_dur": 45},
    {"name": "Amanda", "loc": "The Castro", "avail_start": 660, "avail_end": 735, "min_dur": 60},
    {"name": "Nancy", "loc": "Nob Hill", "avail_start": 45, "avail_end": 240, "min_dur": 45},
    {"name": "Rebecca", "loc": "Sunset District", "avail_start": 0, "avail_end": 360, "min_dur": 75}
]

# Create Z3 variables for meetings 1 to 10
active_vars = [Bool(f"active{i}") for i in range(1, 11)]
time_vars = [Int(f"time{i}") for i in range(1, 11)]
duration_vars = [Int(f"duration{i}") for i in range(1, 11)]

s = Optimize()

# Constraints for meetings 1 to 10
for idx in range(1, 11):
    m_info = meetings[idx]
    a = active_vars[idx-1]
    t = time_vars[idx-1]
    d = duration_vars[idx-1]
    
    # If active, time must be in window and duration must be at least min_dur
    s.add(Implies(a, t >= m_info["avail_start"]))
    s.add(Implies(a, t + d <= m_info["avail_end"]))
    s.add(Implies(a, d == m_info["min_dur"]))  # Fix duration to min_dur if active

# Travel constraints from start (index0) to each meeting j
start_loc = meetings[0]["loc"]
for j in range(1, 11):
    j_loc = meetings[j]["loc"]
    travel_time = travel_times[start_loc][j_loc]
    a_j = active_vars[j-1]
    t_j = time_vars[j-1]
    s.add(Implies(a_j, t_j >= travel_time))

# Travel constraints between meetings i and j (i, j from 1 to 10, i < j)
for i in range(1, 11):
    for j in range(i+1, 11):
        loc_i = meetings[i]["loc"]
        loc_j = meetings[j]["loc"]
        travel_ij = travel_times[loc_i][loc_j]
        travel_ji = travel_times[loc_j][loc_i]
        
        a_i = active_vars[i-1]
        a_j = active_vars[j-1]
        t_i = time_vars[i-1]
        t_j = time_vars[j-1]
        d_i = duration_vars[i-1]
        d_j = duration_vars[j-1]
        
        # If both meetings are active, they must not overlap and account for travel
        constraint = Implies(
            And(a_i, a_j),
            Or(
                And(t_i < t_j, t_j >= t_i + d_i + travel_ij),
                And(t_j < t_i, t_i >= t_j + d_j + travel_ji)
            )
        )
        s.add(constraint)

# Maximize the number of active meetings
total_meetings = Sum([If(a, 1, 0) for a in active_vars])
s.maximize(total_meetings)

# Solve the problem
if s.check() == sat:
    model = s.model()
    itinerary = []
    for idx in range(1, 11):
        if model[active_vars[idx-1]]:
            t_val = model[time_vars[idx-1]]
            d_val = model[duration_vars[idx-1]]
            if t_val is not None and d_val is not None:
                start_min = t_val.as_long()
                dur_min = d_val.as_long()
                end_min = start_min + dur_min
                start_hour = 9 + start_min // 60
                start_minute = start_min % 60
                end_hour = 9 + end_min // 60
                end_minute = end_min % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": meetings[idx]["name"],
                    "start_time": start_str,
                    "end_time": end_str
                })
    # Sort itinerary by start_time
    itinerary.sort(key=lambda x: (int(x['start_time'].split(':')[0]), int(x['start_time'].split(':')[1])))
    print('SOLUTION:')
    print(json.dumps({"itinerary": itinerary}))
else:
    print("SOLUTION:")
    print(json.dumps({"itinerary": []}))