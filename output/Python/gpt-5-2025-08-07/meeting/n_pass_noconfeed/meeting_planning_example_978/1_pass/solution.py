import json
from copy import deepcopy

def parse_time(t):
    t = t.strip().upper()
    if t.endswith('AM') or t.endswith('PM'):
        ampm = t[-2:]
        hm = t[:-2]
    else:
        # already 24h like '13:30'
        ampm = None
        hm = t
    h, m = hm.split(':')
    h = int(h)
    m = int(m)
    if ampm == 'AM':
        if h == 12:
            h = 0
    elif ampm == 'PM':
        if h != 12:
            h += 12
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (directed, in minutes)
travel = {
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "Financial District": 5,
        "Russian Hill": 8,
        "Marina District": 12,
        "Richmond District": 21,
        "Pacific Heights": 11,
        "Haight-Ashbury": 21,
        "Presidio": 20,
        "Nob Hill": 10,
        "The Castro": 25
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8,
        "Financial District": 11,
        "Russian Hill": 7,
        "Marina District": 9,
        "Richmond District": 18,
        "Pacific Heights": 12,
        "Haight-Ashbury": 22,
        "Presidio": 17,
        "Nob Hill": 11,
        "The Castro": 27
    },
    "Financial District": {
        "Embarcadero": 4,
        "Fisherman's Wharf": 10,
        "Russian Hill": 11,
        "Marina District": 15,
        "Richmond District": 21,
        "Pacific Heights": 13,
        "Haight-Ashbury": 19,
        "Presidio": 22,
        "Nob Hill": 8,
        "The Castro": 20
    },
    "Russian Hill": {
        "Embarcadero": 8,
        "Fisherman's Wharf": 7,
        "Financial District": 11,
        "Marina District": 7,
        "Richmond District": 14,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Presidio": 14,
        "Nob Hill": 5,
        "The Castro": 21
    },
    "Marina District": {
        "Embarcadero": 14,
        "Fisherman's Wharf": 10,
        "Financial District": 17,
        "Russian Hill": 8,
        "Richmond District": 11,
        "Pacific Heights": 7,
        "Haight-Ashbury": 16,
        "Presidio": 10,
        "Nob Hill": 12,
        "The Castro": 22
    },
    "Richmond District": {
        "Embarcadero": 19,
        "Fisherman's Wharf": 18,
        "Financial District": 22,
        "Russian Hill": 13,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Haight-Ashbury": 10,
        "Presidio": 7,
        "Nob Hill": 17,
        "The Castro": 16
    },
    "Pacific Heights": {
        "Embarcadero": 10,
        "Fisherman's Wharf": 13,
        "Financial District": 13,
        "Russian Hill": 7,
        "Marina District": 6,
        "Richmond District": 12,
        "Haight-Ashbury": 11,
        "Presidio": 11,
        "Nob Hill": 8,
        "The Castro": 16
    },
    "Haight-Ashbury": {
        "Embarcadero": 20,
        "Fisherman's Wharf": 23,
        "Financial District": 21,
        "Russian Hill": 17,
        "Marina District": 17,
        "Richmond District": 10,
        "Pacific Heights": 12,
        "Presidio": 15,
        "Nob Hill": 15,
        "The Castro": 6
    },
    "Presidio": {
        "Embarcadero": 20,
        "Fisherman's Wharf": 19,
        "Financial District": 23,
        "Russian Hill": 14,
        "Marina District": 11,
        "Richmond District": 7,
        "Pacific Heights": 11,
        "Haight-Ashbury": 15,
        "Nob Hill": 18,
        "The Castro": 21
    },
    "Nob Hill": {
        "Embarcadero": 9,
        "Fisherman's Wharf": 10,
        "Financial District": 9,
        "Russian Hill": 5,
        "Marina District": 11,
        "Richmond District": 14,
        "Pacific Heights": 8,
        "Haight-Ashbury": 13,
        "Presidio": 17,
        "The Castro": 17
    },
    "The Castro": {
        "Embarcadero": 22,
        "Fisherman's Wharf": 24,
        "Financial District": 21,
        "Russian Hill": 18,
        "Marina District": 21,
        "Richmond District": 16,
        "Pacific Heights": 16,
        "Haight-Ashbury": 6,
        "Presidio": 20,
        "Nob Hill": 16
    }
}

# People constraints
people = [
    {"name": "Stephanie", "location": "Fisherman's Wharf", "start": "3:30PM", "end": "10:00PM", "min_minutes": 30},
    {"name": "Lisa", "location": "Financial District", "start": "10:45AM", "end": "5:15PM", "min_minutes": 15},
    {"name": "Melissa", "location": "Russian Hill", "start": "5:00PM", "end": "9:45PM", "min_minutes": 120},
    {"name": "Betty", "location": "Marina District", "start": "10:45AM", "end": "2:15PM", "min_minutes": 60},
    {"name": "Sarah", "location": "Richmond District", "start": "4:15PM", "end": "7:30PM", "min_minutes": 105},
    {"name": "Daniel", "location": "Pacific Heights", "start": "6:30PM", "end": "9:45PM", "min_minutes": 60},
    {"name": "Joshua", "location": "Haight-Ashbury", "start": "9:00AM", "end": "3:30PM", "min_minutes": 15},
    {"name": "Joseph", "location": "Presidio", "start": "7:00AM", "end": "1:00PM", "min_minutes": 45},
    {"name": "Andrew", "location": "Nob Hill", "start": "7:45PM", "end": "10:00PM", "min_minutes": 105},
    {"name": "John", "location": "The Castro", "start": "1:15PM", "end": "7:45PM", "min_minutes": 45}
]

# Convert times to minutes
for p in people:
    p['window_start'] = parse_time(p['start'])
    p['window_end'] = parse_time(p['end'])

start_location = "Embarcadero"
start_time = parse_time("9:00AM")

# Sort people by window end to guide search
people_sorted = sorted(people, key=lambda x: x['window_end'])

# Map name to index for bitmasking
name_to_idx = {p['name']: i for i, p in enumerate(people_sorted)}

best_solution = {
    "count": 0,
    "total_meet": 0,
    "total_travel": 0,
    "end_time": start_time,
    "names": tuple(),
    "itinerary": []
}

def can_reach_later(cur_time, cur_loc, person):
    # Quick feasibility check: even if we left immediately, can we start by latest start?
    t = travel[cur_loc][person['location']]
    latest_start = person['window_end'] - person['min_minutes']
    return cur_time + t <= latest_start

def compare_solutions(sol_a, sol_b):
    # Return True if sol_a is better than sol_b
    keys = ['count', 'total_meet']
    for k in keys:
        if sol_a[k] != sol_b[k]:
            return sol_a[k] > sol_b[k]
    # minimize travel
    if sol_a['total_travel'] != sol_b['total_travel']:
        return sol_a['total_travel'] < sol_b['total_travel']
    # earlier finish
    if sol_a['end_time'] != sol_b['end_time']:
        return sol_a['end_time'] < sol_b['end_time']
    # deterministic tie-breaker by names lexicographically
    return tuple(sorted(sol_a['names'])) < tuple(sorted(sol_b['names']))

def dfs(cur_time, cur_loc, visited_mask, itinerary, total_meet, total_travel):
    global best_solution

    # Update best solution with current
    current_names = tuple(people_sorted[i]['name'] for i in range(len(people_sorted)) if (visited_mask >> i) & 1)
    current_solution = {
        "count": len(current_names),
        "total_meet": total_meet,
        "total_travel": total_travel,
        "end_time": cur_time,
        "names": current_names,
        "itinerary": deepcopy(itinerary)
    }
    if compare_solutions(current_solution, best_solution):
        best_solution = current_solution

    # Upper bound pruning: max additional meetings possible is remaining people count
    remaining = len(people_sorted) - len(current_names)
    if len(current_names) + remaining < best_solution['count']:
        return

    # Candidate next meetings: filter by feasibility from current state
    candidates = []
    for i, person in enumerate(people_sorted):
        if (visited_mask >> i) & 1:
            continue
        if person['location'] not in travel[cur_loc]:
            continue
        if not can_reach_later(cur_time, cur_loc, person):
            continue
        candidates.append((person['window_end'], i, person))
    # Sort by earliest window end to focus on tight windows first
    candidates.sort(key=lambda x: x[0])

    for _, i, person in candidates:
        t_travel = travel[cur_loc][person['location']]
        arrival = cur_time + t_travel
        start = max(arrival, person['window_start'])
        end = start + person['min_minutes']
        if end > person['window_end']:
            continue
        # Build new itinerary entry
        itinerary.append({
            "action": "meet",
            "location": person['location'],
            "person": person['name'],
            "start_time": fmt_time(start),
            "end_time": fmt_time(end)
        })
        dfs(end, person['location'], visited_mask | (1 << i), itinerary, total_meet + person['min_minutes'], total_travel + t_travel)
        itinerary.pop()

# Start DFS
dfs(start_time, start_location, 0, [], 0, 0)

# Prepare output JSON
output = {
    "itinerary": best_solution["itinerary"]
}

print(json.dumps(output, ensure_ascii=False))