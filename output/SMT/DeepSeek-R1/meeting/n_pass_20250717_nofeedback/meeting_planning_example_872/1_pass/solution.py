import z3

def parse_time(time_str):
    if time_str.endswith("AM") or time_str.endswith("PM"):
        time_part = time_str[:-2].strip()
        period = time_str[-2:]
        hour_str, minute_str = time_part.split(':')
        hour = int(hour_str)
        minute = int(minute_str)
        if period == "PM" and hour != 12:
            hour += 12
        if period == "AM" and hour == 12:
            hour = 0
        return hour * 60 + minute
    else:
        raise ValueError(f"Unsupported time format: {time_str}")

friends = [
    ("Karen", "Haight-Ashbury", "9:00PM", "9:45PM", 45),
    ("Jessica", "Nob Hill", "1:45PM", "9:00PM", 90),
    ("Brian", "Russian Hill", "3:30PM", "9:45PM", 60),
    ("Kenneth", "North Beach", "9:45AM", "9:00PM", 30),
    ("Jason", "Chinatown", "8:15AM", "11:45AM", 75),
    ("Stephanie", "Union Square", "2:45PM", "6:45PM", 105),
    ("Kimberly", "Embarcadero", "9:45AM", "7:30PM", 75),
    ("Steven", "Financial District", "7:15AM", "9:15PM", 60),
    ("Mark", "Marina District", "10:15AM", "1:00PM", 75)
]

meetings_info = []
for friend in friends:
    name, loc, start_str, end_str, dur = friend
    start_min = parse_time(start_str)
    end_min = parse_time(end_str)
    meetings_info.append((name, loc, start_min, end_min, dur))

travel_time_dict = {
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Marina District"): 11,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Marina District"): 11,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Marina District"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Marina District"): 9,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Marina District"): 12,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Marina District"): 18,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Marina District"): 12,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Marina District"): 15,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Financial District"): 17
}

s = z3.Optimize()

num_meetings = len(meetings_info)
start_node = 0
end_node = num_meetings + 1
all_nodes = list(range(0, num_meetings + 2))

do = [z3.Bool(f"do_{i}") for i in range(num_meetings)]
arc = {}
for i in range(0, num_meetings + 1):
    for j in range(1, num_meetings + 2):
        if i == j:
            continue
        arc[(i, j)] = z3.Bool(f"arc_{i}_{j}")

time_vars = [z3.Int(f"time_{i}") for i in range(num_meetings)]

start_time = 540

s.add(z3.Sum([z3.If(arc[(start_node, j)], 1, 0) for j in range(1, num_meetings + 2)]) == 1)
s.add(z3.Sum([z3.If(arc[(i, end_node)], 1, 0) for i in range(0, num_meetings + 1)]) == 1)

for i in range(num_meetings):
    meeting_idx = i + 1
    incoming = [arc[(j, meeting_idx)] for j in range(0, num_meetings + 1) if j != meeting_idx]
    outgoing = [arc[(meeting_idx, j)] for j in range(1, num_meetings + 2) if j != meeting_idx]
    
    s.add(z3.Implies(do[i], z3.Sum([z3.If(a, 1, 0) for a in incoming]) == 1))
    s.add(z3.Implies(do[i], z3.Sum([z3.If(a, 1, 0) for a in outgoing]) == 1))
    s.add(z3.Implies(z3.Not(do[i]), z3.Sum([z3.If(a, 1, 0) for a in incoming]) == 0))
    s.add(z3.Implies(z3.Not(do[i]), z3.Sum([z3.If(a, 1, 0) for a in outgoing]) == 0))
    
    name, loc, start_avail, end_avail, min_dur = meetings_info[i]
    s.add(z3.Implies(do[i], time_vars[i] >= start_avail))
    s.add(z3.Implies(do[i], time_vars[i] + min_dur <= end_avail))

for i in range(0, num_meetings + 1):
    for j in range(1, num_meetings + 1):
        if i == j:
            continue
        if (i, j) not in arc:
            continue
        arc_var = arc[(i, j)]
        if i == start_node:
            loc_i = "Presidio"
            loc_j = meetings_info[j - 1][1]
            travel = travel_time_dict.get((loc_i, loc_j))
            if travel is None:
                raise Exception(f"Travel time from {loc_i} to {loc_j} not found")
            s.add(z3.Implies(arc_var, time_vars[j - 1] >= start_time + travel))
        else:
            loc_i = meetings_info[i - 1][1]
            loc_j = meetings_info[j - 1][1]
            travel = travel_time_dict.get((loc_i, loc_j))
            if travel is None:
                raise Exception(f"Travel time from {loc_i} to {loc_j} not found")
            min_dur_i = meetings_info[i - 1][4]
            s.add(z3.Implies(arc_var, time_vars[j - 1] >= time_vars[i - 1] + min_dur_i + travel))

obj = z3.Sum([z3.If(do_i, 1, 0) for do_i in do])
s.maximize(obj)

if s.check() == z3.sat:
    model = s.model()
    itinerary = []
    for i in range(num_meetings):
        if model[do[i]] == True:
            name, loc, start_avail, end_avail, min_dur = meetings_info[i]
            start_min = model[time_vars[i]].as_long()
            hours = start_min // 60
            minutes = start_min % 60
            start_time_str = f"{hours:02d}:{minutes:02d}"
            end_min = start_min + min_dur
            hours_end = end_min // 60
            minutes_end = end_min % 60
            end_time_str = f"{hours_end:02d}:{minutes_end:02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_time_str,
                "end_time": end_time_str
            })
    itinerary_sorted = sorted(itinerary, key=lambda x: x['start_time'])
    print("SOLUTION:")
    print(f'{{"itinerary": {itinerary_sorted}}}')
else:
    print("No solution found")