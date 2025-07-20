from z3 import *

def time_str_to_minutes_since_9am(s):
    s = s.strip().upper()
    if s.endswith("PM"):
        if s.split(':')[0] == "12":
            hours = 12
        else:
            hours = int(s.split(':')[0]) + 12
        minutes_str = s.split(':')[1].replace("PM", "").strip()
        minutes = int(minutes_str)
    else:
        if s.split(':')[0] == "12":
            hours = 0
        else:
            hours = int(s.split(':')[0])
        minutes_str = s.split(':')[1].replace("AM", "").strip()
        minutes = int(minutes_str)
    total_minutes = hours * 60 + minutes
    ref_9am = 9 * 60
    return total_minutes - ref_9am

travel_data = """
Union Square to Presidio: 24.
Union Square to Alamo Square: 15.
Union Square to Marina District: 18.
Union Square to Financial District: 9.
Union Square to Nob Hill: 9.
Union Square to Sunset District: 27.
Union Square to Chinatown: 7.
Union Square to Russian Hill: 13.
Union Square to North Beach: 10.
Union Square to Haight-Ashbury: 18.
Presidio to Union Square: 22.
Presidio to Alamo Square: 19.
Presidio to Marina District: 11.
Presidio to Financial District: 23.
Presidio to Nob Hill: 18.
Presidio to Sunset District: 15.
Presidio to Chinatown: 21.
Presidio to Russian Hill: 14.
Presidio to North Beach: 18.
Presidio to Haight-Ashbury: 15.
Alamo Square to Union Square: 14.
Alamo Square to Presidio: 17.
Alamo Square to Marina District: 15.
Alamo Square to Financial District: 17.
Alamo Square to Nob Hill: 11.
Alamo Square to Sunset District: 16.
Alamo Square to Chinatown: 15.
Alamo Square to Russian Hill: 13.
Alamo Square to North Beach: 15.
Alamo Square to Haight-Ashbury: 5.
Marina District to Union Square: 16.
Marina District to Presidio: 10.
Marina District to Alamo Square: 15.
Marina District to Financial District: 17.
Marina District to Nob Hill: 12.
Marina District to Sunset District: 19.
Marina District to Chinatown: 15.
Marina District to Russian Hill: 8.
Marina District to North Beach: 11.
Marina District to Haight-Ashbury: 16.
Financial District to Union Square: 9.
Financial District to Presidio: 22.
Financial District to Alamo Square: 17.
Financial District to Marina District: 15.
Financial District to Nob Hill: 8.
Financial District to Sunset District: 30.
Financial District to Chinatown: 5.
Financial District to Russian Hill: 11.
Financial District to North Beach: 7.
Financial District to Haight-Ashbury: 19.
Nob Hill to Union Square: 7.
Nob Hill to Presidio: 17.
Nob Hill to Alamo Square: 11.
Nob Hill to Marina District: 11.
Nob Hill to Financial District: 9.
Nob Hill to Sunset District: 24.
Nob Hill to Chinatown: 6.
Nob Hill to Russian Hill: 5.
Nob Hill to North Beach: 8.
Nob Hill to Haight-Ashbury: 13.
Sunset District to Union Square: 30.
Sunset District to Presidio: 16.
Sunset District to Alamo Square: 17.
Sunset District to Marina District: 21.
Sunset District to Financial District: 30.
Sunset District to Nob Hill: 27.
Sunset District to Chinatown: 30.
Sunset District to Russian Hill: 24.
Sunset District to North Beach: 28.
Sunset District to Haight-Ashbury: 15.
Chinatown to Union Square: 7.
Chinatown to Presidio: 19.
Chinatown to Alamo Square: 17.
Chinatown to Marina District: 12.
Chinatown to Financial District: 5.
Chinatown to Nob Hill: 9.
Chinatown to Sunset District: 29.
Chinatown to Russian Hill: 7.
Chinatown to North Beach: 3.
Chinatown to Haight-Ashbury: 19.
Russian Hill to Union Square: 10.
Russian Hill to Presidio: 14.
Russian Hill to Alamo Square: 15.
Russian Hill to Marina District: 7.
Russian Hill to Financial District: 11.
Russian Hill to Nob Hill: 5.
Russian Hill to Sunset District: 23.
Russian Hill to Chinatown: 9.
Russian Hill to North Beach: 5.
Russian Hill to Haight-Ashbury: 17.
North Beach to Union Square: 7.
North Beach to Presidio: 17.
North Beach to Alamo Square: 16.
North Beach to Marina District: 9.
North Beach to Financial District: 8.
North Beach to Nob Hill: 7.
North Beach to Sunset District: 27.
North Beach to Chinatown: 6.
North Beach to Russian Hill: 4.
North Beach to Haight-Ashbury: 18.
Haight-Ashbury to Union Square: 19.
Haight-Ashbury to Presidio: 15.
Haight-Ashbury to Alamo Square: 5.
Haight-Ashbury to Marina District: 17.
Haight-Ashbury to Financial District: 21.
Haight-Ashbury to Nob Hill: 15.
Haight-Ashbury to Sunset District: 15.
Haight-Ashbury to Chinatown: 19.
Haight-Ashbury to Russian Hill: 17.
Haight-Ashbury to North Beach: 19.
"""

travel_dict = {}
lines = travel_data.strip().split('\n')
for line in lines:
    line = line.strip()
    if not line:
        continue
    parts = line.split(':')
    if len(parts) < 2:
        continue
    time_val = int(parts[-1].strip().rstrip('.'))
    from_to_str = parts[0].strip()
    if " to " in from_to_str:
        from_loc, to_loc = from_to_str.split(" to ", 1)
        from_loc = from_loc.strip()
        to_loc = to_loc.strip()
        key = (from_loc, to_loc)
        travel_dict[key] = time_val

friends = [
    {'name': 'Kimberly', 'location': 'Presidio', 
     'start_win': time_str_to_minutes_since_9am("3:30PM"), 
     'end_win': time_str_to_minutes_since_9am("4:00PM"), 
     'min_duration': 15},
    {'name': 'Elizabeth', 'location': 'Alamo Square', 
     'start_win': time_str_to_minutes_since_9am("7:15PM"), 
     'end_win': time_str_to_minutes_since_9am("8:15PM"), 
     'min_duration': 15},
    {'name': 'Joshua', 'location': 'Marina District', 
     'start_win': time_str_to_minutes_since_9am("10:30AM"), 
     'end_win': time_str_to_minutes_since_9am("2:15PM"), 
     'min_duration': 45},
    {'name': 'Sandra', 'location': 'Financial District', 
     'start_win': time_str_to_minutes_since_9am("7:30PM"), 
     'end_win': time_str_to_minutes_since_9am("8:15PM"), 
     'min_duration': 45},
    {'name': 'Kenneth', 'location': 'Nob Hill', 
     'start_win': time_str_to_minutes_since_9am("12:45PM"), 
     'end_win': time_str_to_minutes_since_9am("9:45PM"), 
     'min_duration': 30},
    {'name': 'Betty', 'location': 'Sunset District', 
     'start_win': time_str_to_minutes_since_9am("2:00PM"), 
     'end_win': time_str_to_minutes_since_9am("7:00PM"), 
     'min_duration': 60},
    {'name': 'Deborah', 'location': 'Chinatown', 
     'start_win': time_str_to_minutes_since_9am("5:15PM"), 
     'end_win': time_str_to_minutes_since_9am("8:30PM"), 
     'min_duration': 15},
    {'name': 'Barbara', 'location': 'Russian Hill', 
     'start_win': time_str_to_minutes_since_9am("5:30PM"), 
     'end_win': time_str_to_minutes_since_9am("9:15PM"), 
     'min_duration': 120},
    {'name': 'Steven', 'location': 'North Beach', 
     'start_win': time_str_to_minutes_since_9am("5:45PM"), 
     'end_win': time_str_to_minutes_since_9am("8:45PM"), 
     'min_duration': 90},
    {'name': 'Daniel', 'location': 'Haight-Ashbury', 
     'start_win': time_str_to_minutes_since_9am("6:30PM"), 
     'end_win': time_str_to_minutes_since_9am("6:45PM"), 
     'min_duration': 15}
]

n_friends = len(friends)

s = Optimize()

meet = [Bool(f"meet_{i}") for i in range(n_friends)]
start = [Int(f"start_{i}") for i in range(n_friends)]
end = [Int(f"end_{i}") for i in range(n_friends)]

n_events = n_friends + 1
dummy_start_index = 0
friend_event_offset = 1

before = [[Bool(f"before_{i}_{j}") for j in range(n_events)] for i in range(n_events)]

for j in range(n_friends):
    event_j = j + friend_event_offset
    s.add(Implies(meet[j], before[dummy_start_index][event_j]))
    s.add(Implies(meet[j], Not(before[event_j][dummy_start_index])))

for i in range(n_friends):
    event_i = i + friend_event_offset
    for j in range(n_friends):
        if i == j:
            continue
        event_j = j + friend_event_offset
        s.add(Implies(And(meet[i], meet[j]), 
                     before[event_i][event_j] == Not(before[event_j][event_i])))
        s.add(Implies(And(meet[i], meet[j]), 
                     Or(before[event_i][event_j], before[event_j][event_i])))

for i in range(n_events):
    for j in range(n_events):
        if i == j:
            continue
        for k in range(n_events):
            if i == k or j == k:
                continue
            cond_i = True
            cond_j = True
            cond_k = True
            if i != dummy_start_index:
                cond_i = meet[i - friend_event_offset]
            if j != dummy_start_index:
                cond_j = meet[j - friend_event_offset]
            if k != dummy_start_index:
                cond_k = meet[k - friend_event_offset]
            condition = And(cond_i, cond_j, cond_k)
            s.add(Implies(condition, 
                          Implies(And(before[i][j], before[j][k]), 
                                  before[i][k])))

for j in range(n_friends):
    s.add(Implies(meet[j], start[j] >= friends[j]['start_win']))
    s.add(Implies(meet[j], end[j] == start[j] + friends[j]['min_duration']))
    s.add(Implies(meet[j], end[j] <= friends[j]['end_win']))

for j in range(n_friends):
    event_j = j + friend_event_offset
    for i in range(n_events):
        if i == event_j:
            continue
        cond_i_met = True
        if i != dummy_start_index:
            friend_i_index = i - friend_event_offset
            cond_i_met = meet[friend_i_index]
        condition = And(meet[j], cond_i_met, before[i][event_j])
        if i == dummy_start_index:
            from_loc = 'Union Square'
            to_loc = friends[j]['location']
            travel_time = travel_dict.get((from_loc, to_loc))
            if travel_time is None:
                travel_time = 1000
            s.add(Implies(condition, start[j] >= travel_time))
        else:
            friend_i_index = i - friend_event_offset
            from_loc = friends[friend_i_index]['location']
            to_loc = friends[j]['location']
            travel_time = travel_dict.get((from_loc, to_loc))
            if travel_time is None:
                travel_time = 1000
            s.add(Implies(condition, start[j] >= end[friend_i_index] + travel_time))

s.maximize(Sum([If(meet[i], 1, 0) for i in range(n_friends)]))

if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(n_friends):
        if model.eval(meet[i]):
            start_val = model.eval(start[i]).as_long()
            end_val = model.eval(end[i]).as_long()
            total_minutes_start = 9*60 + start_val
            hours_start = total_minutes_start // 60
            minutes_start = total_minutes_start % 60
            start_time_str = f"{int(hours_start)}:{int(minutes_start):02d}"
            total_minutes_end = 9*60 + end_val
            hours_end = total_minutes_end // 60
            minutes_end = total_minutes_end % 60
            end_time_str = f"{int(hours_end)}:{int(minutes_end):02d}"
            itinerary.append({
                "action": "meet",
                "person": friends[i]['name'],
                "start_time": start_time_str,
                "end_time": end_time_str
            })
    itinerary_sorted = sorted(itinerary, key=lambda x: x['start_time'])
    print('SOLUTION:')
    print(f'{{"itinerary": {itinerary_sorted}}}')
else:
    print("No solution found")