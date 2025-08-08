from z3 import *
import itertools

# Define travel times between locations
travel_dict = {
    "Sunset": {
        "Alamo": 17,
        "Russian": 24,
        "Presidio": 16,
        "Financial": 30
    },
    "Alamo": {
        "Sunset": 16,
        "Russian": 13,
        "Presidio": 18,
        "Financial": 17
    },
    "Russian": {
        "Sunset": 23,
        "Alamo": 15,
        "Presidio": 14,
        "Financial": 11
    },
    "Presidio": {
        "Sunset": 15,
        "Alamo": 18,
        "Russian": 14,
        "Financial": 23
    },
    "Financial": {
        "Sunset": 31,
        "Alamo": 17,
        "Russian": 10,
        "Presidio": 22
    }
}

# Define meetings with their constraints
meetings_info = [
    {"name": "Kevin", "loc": "Alamo", "dur": 75, "min_start": 557, "max_start": 1215},
    {"name": "Kimberly", "loc": "Russian", "dur": 30, "min_start": 564, "max_start": 720},
    {"name": "Joseph", "loc": "Presidio", "dur": 45, "min_start": 1110, "max_start": 1110},
    {"name": "Thomas", "loc": "Financial", "dur": 45, "min_start": 1140, "max_start": 1260}
]

# Try combinations in descending order of size (4, 3, 2, 1)
all_meetings = [0, 1, 2, 3]
found_schedule = None

for size in range(4, 0, -1):
    for subset in itertools.combinations(all_meetings, size):
        solver = Solver()
        s_vars = [Int(f's_{i}') for i in subset]
        meeting_list = []
        
        # Add constraints for each meeting in the subset
        for idx, (s, meeting_idx) in enumerate(zip(s_vars, subset)):
            info = meetings_info[meeting_idx]
            solver.add(s >= info["min_start"])
            solver.add(s <= info["max_start"])
            if info["name"] == "Joseph":
                solver.add(s == 1110)
            meeting_list.append((s, meeting_idx, info))
        
        # Add pairwise constraints for every two meetings in the subset
        n = len(subset)
        for i in range(n):
            for j in range(i+1, n):
                s_i = s_vars[i]
                s_j = s_vars[j]
                info_i = meetings_info[subset[i]]
                info_j = meetings_info[subset[j]]
                loc_i = info_i["loc"]
                loc_j = info_j["loc"]
                travel_ij = travel_dict[loc_i][loc_j]
                travel_ji = travel_dict[loc_j][loc_i]
                solver.add(Or(
                    s_j >= s_i + info_i["dur"] + travel_ij,
                    s_i >= s_j + info_j["dur"] + travel_ji
                ))
        
        if solver.check() == sat:
            model = solver.model()
            itinerary = []
            for s_var, meeting_idx, info in meeting_list:
                start_val = model[s_var].as_long()
                end_val = start_val + info["dur"]
                hours_s = start_val // 60
                minutes_s = start_val % 60
                start_str = f"{hours_s:02d}:{minutes_s:02d}"
                hours_e = end_val // 60
                minutes_e = end_val % 60
                end_str = f"{hours_e:02d}:{minutes_e:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": info["name"],
                    "start_time": start_str,
                    "end_time": end_str
                })
            itinerary_sorted = sorted(itinerary, key=lambda x: x["start_time"])
            found_schedule = itinerary_sorted
            break
    if found_schedule is not None:
        break

# If no schedule is found, default to an empty itinerary
if found_schedule is None:
    found_schedule = []

# Output the solution in JSON format
print("SOLUTION:")
print({"itinerary": found_schedule})