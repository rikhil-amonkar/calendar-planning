import json
from functools import lru_cache

def hm(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times (minutes)
D = {}
def add(frm, to, m):
    D[(frm, to)] = m

# Locations
LOCATIONS = [
    "The Castro",
    "Alamo Square",
    "Richmond District",
    "Financial District",
    "Union Square",
    "Fisherman's Wharf",
    "Marina District",
    "Haight-Ashbury",
    "Mission District",
    "Pacific Heights",
    "Golden Gate Park",
]

# Define all given directed travel times
add("The Castro", "Alamo Square", 8)
add("The Castro", "Richmond District", 16)
add("The Castro", "Financial District", 21)
add("The Castro", "Union Square", 19)
add("The Castro", "Fisherman's Wharf", 24)
add("The Castro", "Marina District", 21)
add("The Castro", "Haight-Ashbury", 6)
add("The Castro", "Mission District", 7)
add("The Castro", "Pacific Heights", 16)
add("The Castro", "Golden Gate Park", 11)

add("Alamo Square", "The Castro", 8)
add("Alamo Square", "Richmond District", 11)
add("Alamo Square", "Financial District", 17)
add("Alamo Square", "Union Square", 14)
add("Alamo Square", "Fisherman's Wharf", 19)
add("Alamo Square", "Marina District", 15)
add("Alamo Square", "Haight-Ashbury", 5)
add("Alamo Square", "Mission District", 10)
add("Alamo Square", "Pacific Heights", 10)
add("Alamo Square", "Golden Gate Park", 9)

add("Richmond District", "The Castro", 16)
add("Richmond District", "Alamo Square", 13)
add("Richmond District", "Financial District", 22)
add("Richmond District", "Union Square", 21)
add("Richmond District", "Fisherman's Wharf", 18)
add("Richmond District", "Marina District", 9)
add("Richmond District", "Haight-Ashbury", 10)
add("Richmond District", "Mission District", 20)
add("Richmond District", "Pacific Heights", 10)
add("Richmond District", "Golden Gate Park", 9)

add("Financial District", "The Castro", 20)
add("Financial District", "Alamo Square", 17)
add("Financial District", "Richmond District", 21)
add("Financial District", "Union Square", 9)
add("Financial District", "Fisherman's Wharf", 10)
add("Financial District", "Marina District", 15)
add("Financial District", "Haight-Ashbury", 19)
add("Financial District", "Mission District", 17)
add("Financial District", "Pacific Heights", 13)
add("Financial District", "Golden Gate Park", 23)

add("Union Square", "The Castro", 17)
add("Union Square", "Alamo Square", 15)
add("Union Square", "Richmond District", 20)
add("Union Square", "Financial District", 9)
add("Union Square", "Fisherman's Wharf", 15)
add("Union Square", "Marina District", 18)
add("Union Square", "Haight-Ashbury", 18)
add("Union Square", "Mission District", 14)
add("Union Square", "Pacific Heights", 15)
add("Union Square", "Golden Gate Park", 22)

add("Fisherman's Wharf", "The Castro", 27)
add("Fisherman's Wharf", "Alamo Square", 21)
add("Fisherman's Wharf", "Richmond District", 18)
add("Fisherman's Wharf", "Financial District", 11)
add("Fisherman's Wharf", "Union Square", 13)
add("Fisherman's Wharf", "Marina District", 9)
add("Fisherman's Wharf", "Haight-Ashbury", 22)
add("Fisherman's Wharf", "Mission District", 22)
add("Fisherman's Wharf", "Pacific Heights", 12)
add("Fisherman's Wharf", "Golden Gate Park", 25)

add("Marina District", "The Castro", 22)
add("Marina District", "Alamo Square", 15)
add("Marina District", "Richmond District", 11)
add("Marina District", "Financial District", 17)
add("Marina District", "Union Square", 16)
add("Marina District", "Fisherman's Wharf", 10)
add("Marina District", "Haight-Ashbury", 16)
add("Marina District", "Mission District", 20)
add("Marina District", "Pacific Heights", 7)
add("Marina District", "Golden Gate Park", 18)

add("Haight-Ashbury", "The Castro", 6)
add("Haight-Ashbury", "Alamo Square", 5)
add("Haight-Ashbury", "Richmond District", 10)
add("Haight-Ashbury", "Financial District", 21)
add("Haight-Ashbury", "Union Square", 19)
add("Haight-Ashbury", "Fisherman's Wharf", 23)
add("Haight-Ashbury", "Marina District", 17)
add("Haight-Ashbury", "Mission District", 11)
add("Haight-Ashbury", "Pacific Heights", 12)
add("Haight-Ashbury", "Golden Gate Park", 7)

add("Mission District", "The Castro", 7)
add("Mission District", "Alamo Square", 11)
add("Mission District", "Richmond District", 20)
add("Mission District", "Financial District", 15)
add("Mission District", "Union Square", 15)
add("Mission District", "Fisherman's Wharf", 22)
add("Mission District", "Marina District", 19)
add("Mission District", "Haight-Ashbury", 12)
add("Mission District", "Pacific Heights", 16)
add("Mission District", "Golden Gate Park", 17)

add("Pacific Heights", "The Castro", 16)
add("Pacific Heights", "Alamo Square", 10)
add("Pacific Heights", "Richmond District", 12)
add("Pacific Heights", "Financial District", 13)
add("Pacific Heights", "Union Square", 12)
add("Pacific Heights", "Fisherman's Wharf", 13)
add("Pacific Heights", "Marina District", 6)
add("Pacific Heights", "Haight-Ashbury", 11)
add("Pacific Heights", "Mission District", 15)
add("Pacific Heights", "Golden Gate Park", 15)

add("Golden Gate Park", "The Castro", 13)
add("Golden Gate Park", "Alamo Square", 9)
add("Golden Gate Park", "Richmond District", 7)
add("Golden Gate Park", "Financial District", 26)
add("Golden Gate Park", "Union Square", 22)
add("Golden Gate Park", "Fisherman's Wharf", 24)
add("Golden Gate Park", "Marina District", 16)
add("Golden Gate Park", "Haight-Ashbury", 7)
add("Golden Gate Park", "Mission District", 17)
add("Golden Gate Park", "Pacific Heights", 16)

# People constraints
people = [
    {
        "name": "William",
        "location": "Alamo Square",
        "start": hm(15, 15),
        "end": hm(17, 15),
        "min": 60,
    },
    {
        "name": "Joshua",
        "location": "Richmond District",
        "start": hm(7, 0),
        "end": hm(20, 0),
        "min": 15,
    },
    {
        "name": "Joseph",
        "location": "Financial District",
        "start": hm(11, 15),
        "end": hm(13, 30),
        "min": 15,
    },
    {
        "name": "David",
        "location": "Union Square",
        "start": hm(16, 45),
        "end": hm(19, 15),
        "min": 45,
    },
    {
        "name": "Brian",
        "location": "Fisherman's Wharf",
        "start": hm(13, 45),
        "end": hm(20, 45),
        "min": 105,
    },
    {
        "name": "Karen",
        "location": "Marina District",
        "start": hm(11, 30),
        "end": hm(18, 30),
        "min": 15,
    },
    {
        "name": "Anthony",
        "location": "Haight-Ashbury",
        "start": hm(7, 15),
        "end": hm(10, 30),
        "min": 30,
    },
    {
        "name": "Matthew",
        "location": "Mission District",
        "start": hm(17, 15),
        "end": hm(19, 15),
        "min": 120,
    },
    {
        "name": "Helen",
        "location": "Pacific Heights",
        "start": hm(8, 0),
        "end": hm(12, 0),
        "min": 75,
    },
    {
        "name": "Jeffrey",
        "location": "Golden Gate Park",
        "start": hm(19, 0),
        "end": hm(21, 30),
        "min": 60,
    },
]

# Map person index for bitmasking
name_to_idx = {p["name"]: i for i, p in enumerate(people)}

# Start state
START_LOCATION = "The Castro"
START_TIME = hm(9, 0)

# Utility to safely get travel time, assuming directed map is complete
def travel_time(a, b):
    if a == b:
        return 0
    t = D.get((a, b))
    if t is None:
        # Fallback to symmetric if missing (shouldn't happen with given data)
        t = D.get((b, a))
    if t is None:
        raise ValueError(f"No travel time between {a} and {b}")
    return t

# Precompute end-of-day as latest end among all people
END_OF_DAY = max(p["end"] for p in people)

# Comparison of solutions
# Each solution is a tuple: (count, total_meeting_minutes, finish_time, total_travel, itinerary_list)
def better(sol_a, sol_b):
    if sol_b is None:
        return True
    if sol_a[0] != sol_b[0]:
        return sol_a[0] > sol_b[0]
    if sol_a[1] != sol_b[1]:
        return sol_a[1] > sol_b[1]
    if sol_a[2] != sol_b[2]:
        return sol_a[2] < sol_b[2]
    if sol_a[3] != sol_b[3]:
        return sol_a[3] < sol_b[3]
    return False

# Memoized search
@lru_cache(maxsize=None)
def search(cur_loc, cur_time, remaining_mask):
    best = (0, 0, cur_time, 0, tuple())  # base: no more meetings
    n = len(people)
    for i in range(n):
        if not (remaining_mask & (1 << i)):
            continue
        p = people[i]
        t_move = travel_time(cur_loc, p["location"])
        arrival = cur_time + t_move
        start = max(arrival, p["start"])
        end = start + p["min"]
        if end > p["end"]:
            continue  # cannot meet
        # Visit person i
        next_mask = remaining_mask & ~(1 << i)
        suffix = search(p["location"], end, next_mask)
        # Build current solution
        count = 1 + suffix[0]
        total_meet = p["min"] + suffix[1]
        finish_time = suffix[2]
        total_travel = t_move + suffix[3]
        itinerary_list = (
            (p["name"], p["location"], start, end),
        ) + suffix[4]
        candidate = (count, total_meet, finish_time, total_travel, itinerary_list)
        if better(candidate, best):
            best = candidate
    return best

def build_itinerary():
    remaining_mask = (1 << len(people)) - 1
    best = search(START_LOCATION, START_TIME, remaining_mask)
    # Convert itinerary tuples to required JSON dicts
    itinerary = []
    cur_loc = START_LOCATION
    cur_time = START_TIME
    for name, loc, start, end in best[4]:
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": minutes_to_str(start),
            "end_time": minutes_to_str(end),
        })
        cur_loc = loc
        cur_time = end
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = build_itinerary()
    print(json.dumps(result, ensure_ascii=False))