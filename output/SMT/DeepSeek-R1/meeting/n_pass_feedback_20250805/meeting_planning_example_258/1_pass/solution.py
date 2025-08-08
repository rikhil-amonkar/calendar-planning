from z3 import *
import itertools

# Travel times between locations
travel_times = {
    ('E', 'P'): 20,
    ('E', 'R'): 21,
    ('E', 'F'): 6,
    ('P', 'E'): 20,
    ('P', 'R'): 7,
    ('P', 'F'): 19,
    ('R', 'E'): 19,
    ('R', 'P'): 7,
    ('R', 'F'): 18,
    ('F', 'E'): 8,
    ('F', 'P'): 17,
    ('F', 'R'): 18
}

# Friend information: location, availability start and end times, and minimum meeting duration
friends_info = {
    'Betty': {'loc': 'P', 'start_avail': 75, 'end_avail': 750, 'dur': 45},
    'David': {'loc': 'R', 'start_avail': 240, 'end_avail': 675, 'dur': 90},
    'Barbara': {'loc': 'F', 'start_avail': 15, 'end_avail': 675, 'dur': 120}
}

# Convert minutes from 9:00 AM to HH:MM format
def minutes_to_time(minutes):
    hour = 9 + minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

# Initialize variables
found_schedule = False
schedule = []

# Attempt to schedule all three friends
for perm in itertools.permutations(['Betty', 'David', 'Barbara']):
    s = Solver()
    s1, s2, s3 = Ints('s1 s2 s3')
    f1, f2, f3 = perm
    info1 = friends_info[f1]
    info2 = friends_info[f2]
    info3 = friends_info[f3]
    
    # Constraints for first meeting
    s.add(s1 >= travel_times[('E', info1['loc'])])
    s.add(s1 >= info1['start_avail'])
    s.add(s1 + info1['dur'] <= info1['end_avail'])
    
    # Constraints for second meeting
    s.add(s2 >= s1 + info1['dur'] + travel_times[(info1['loc'], info2['loc'])])
    s.add(s2 >= info2['start_avail'])
    s.add(s2 + info2['dur'] <= info2['end_avail'])
    
    # Constraints for third meeting
    s.add(s3 >= s2 + info2['dur'] + travel_times[(info2['loc'], info3['loc'])])
    s.add(s3 >= info3['start_avail'])
    s.add(s3 + info3['dur'] <= info3['end_avail'])
    
    if s.check() == sat:
        m = s.model()
        start1 = m.evaluate(s1).as_long()
        start2 = m.evaluate(s2).as_long()
        start3 = m.evaluate(s3).as_long()
        schedule = [
            {"action": "meet", "person": f1, "start_time": minutes_to_time(start1), "end_time": minutes_to_time(start1 + info1['dur'])},
            {"action": "meet", "person": f2, "start_time": minutes_to_time(start2), "end_time": minutes_to_time(start2 + info2['dur'])},
            {"action": "meet", "person": f3, "start_time": minutes_to_time(start3), "end_time": minutes_to_time(start3 + info3['dur'])}
        ]
        found_schedule = True
        break

if not found_schedule:
    # Attempt to schedule any two friends
    subsets = [['Betty', 'David'], ['Betty', 'Barbara'], ['David', 'Barbara']]
    for subset in subsets:
        perms = list(itertools.permutations(subset))
        for perm in perms:
            s = Solver()
            s1, s2 = Ints('s1 s2')
            f1, f2 = perm
            info1 = friends_info[f1]
            info2 = friends_info[f2]
            
            s.add(s1 >= travel_times[('E', info1['loc'])])
            s.add(s1 >= info1['start_avail'])
            s.add(s1 + info1['dur'] <= info1['end_avail'])
            
            s.add(s2 >= s1 + info1['dur'] + travel_times[(info1['loc'], info2['loc'])])
            s.add(s2 >= info2['start_avail'])
            s.add(s2 + info2['dur'] <= info2['end_avail'])
            
            if s.check() == sat:
                m = s.model()
                start1 = m.evaluate(s1).as_long()
                start2 = m.evaluate(s2).as_long()
                schedule = [
                    {"action": "meet", "person": f1, "start_time": minutes_to_time(start1), "end_time": minutes_to_time(start1 + info1['dur'])},
                    {"action": "meet", "person": f2, "start_time": minutes_to_time(start2), "end_time": minutes_to_time(start2 + info2['dur'])}
                ]
                found_schedule = True
                break
        if found_schedule:
            break

if not found_schedule:
    # Attempt to schedule any one friend
    for friend in ['Betty', 'David', 'Barbara']:
        s = Solver()
        s1 = Int('s1')
        info = friends_info[friend]
        s.add(s1 >= travel_times[('E', info['loc'])])
        s.add(s1 >= info['start_avail'])
        s.add(s1 + info['dur'] <= info['end_avail'])
        if s.check() == sat:
            m = s.model()
            start1 = m.evaluate(s1).as_long()
            schedule = [
                {"action": "meet", "person": friend, "start_time": minutes_to_time(start1), "end_time": minutes_to_time(start1 + info['dur'])}
            ]
            found_schedule = True
            break

# Output the schedule in JSON format
if schedule:
    entries = []
    for meeting in schedule:
        entries.append(f'{{"action": "meet", "person": "{meeting["person"]}", "start_time": "{meeting["start_time"]}", "end_time": "{meeting["end_time"]}"}}')
    json_str = '{"itinerary": [' + ', '.join(entries) + ']}'
    print(json_str)
else:
    print('{"itinerary": []}')