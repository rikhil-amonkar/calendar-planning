from z3 import *
import itertools

def min_to_time(minutes):
    total_minutes = minutes
    hours = 9 + total_minutes // 60
    minutes_part = total_minutes % 60
    return f"{hours:02d}:{minutes_part:02d}"

def schedule_k_friends(friends, travel_matrix, location_to_index):
    k = len(friends)
    if k == 0:
        return []
    
    solver = Solver()
    s = [Int(f's_{i}') for i in range(k)]
    f = [Int(f'f_{i}') for i in range(k)]
    
    solver.add(Distinct(f))
    for i in range(k):
        solver.add(f[i] >= 0)
        solver.add(f[i] < k)
    
    locs = [location_to_index[fr['location']] for fr in friends]
    durations_list = [fr['duration'] for fr in friends]
    avail_starts_list = [fr['avail_start'] for fr in friends]
    avail_ends_list = [fr['avail_end'] for fr in friends]
    
    loc_exprs = []
    duration_exprs = []
    avail_start_exprs = []
    avail_end_exprs = []
    
    for i in range(k):
        loc_expr = locs[0]
        for idx in range(1, k):
            loc_expr = If(f[i] == idx, locs[idx], loc_expr)
        loc_exprs.append(loc_expr)
        
        dur_expr = durations_list[0]
        for idx in range(1, k):
            dur_expr = If(f[i] == idx, durations_list[idx], dur_expr)
        duration_exprs.append(dur_expr)
        
        avail_start_expr = avail_starts_list[0]
        for idx in range(1, k):
            avail_start_expr = If(f[i] == idx, avail_starts_list[idx], avail_start_expr)
        avail_start_exprs.append(avail_start_expr)
        
        avail_end_expr = avail_ends_list[0]
        for idx in range(1, k):
            avail_end_expr = If(f[i] == idx, avail_ends_list[idx], avail_end_expr)
        avail_end_exprs.append(avail_end_expr)
    
    # Constraints for the first meeting (position 0)
    tt0 = travel_matrix[0][0]
    for loc_val in [1, 2, 3]:
        tt0 = If(loc_exprs[0] == loc_val, travel_matrix[0][loc_val], tt0)
    solver.add(s[0] >= tt0)
    solver.add(s[0] >= avail_start_exprs[0])
    solver.add(s[0] + duration_exprs[0] <= avail_end_exprs[0])
    
    for i in range(1, k):
        travel_time = travel_matrix[0][0]
        for loc1 in range(4):
            for loc2 in range(4):
                travel_time = If(And(loc_exprs[i-1] == loc1, loc_exprs[i] == loc2), travel_matrix[loc1][loc2], travel_time)
        solver.add(s[i] >= s[i-1] + duration_exprs[i-1] + travel_time)
        solver.add(s[i] >= avail_start_exprs[i])
        solver.add(s[i] + duration_exprs[i] <= avail_end_exprs[i])
    
    if solver.check() == sat:
        model = solver.model()
        f_val = [model.evaluate(f_i).as_long() for f_i in f]
        s_val = [model.evaluate(s_i).as_long() for s_i in s]
        itinerary = []
        for i in range(k):
            friend_idx = f_val[i]
            friend = friends[friend_idx]
            start = s_val[i]
            end = start + friend['duration']
            itinerary.append({
                "action": "meet",
                "person": friend['name'],
                "start_time": min_to_time(start),
                "end_time": min_to_time(end)
            })
        return itinerary
    else:
        return None

def main():
    location_to_index = {
        'Embarcadero': 0,
        'Fisherman\'s Wharf': 1,
        'Presidio': 2,
        'Richmond District': 3
    }
    travel_matrix = [
        [0, 6, 20, 21],
        [8, 0, 17, 18],
        [20, 19, 0, 7],
        [19, 18, 7, 0]
    ]
    barbara = {
        'name': 'Barbara',
        'location': 'Fisherman\'s Wharf',
        'duration': 120,
        'avail_start': 15,
        'avail_end': 675
    }
    betty = {
        'name': 'Betty',
        'location': 'Presidio',
        'duration': 45,
        'avail_start': 75,
        'avail_end': 750
    }
    david = {
        'name': 'David',
        'location': 'Richmond District',
        'duration': 90,
        'avail_start': 240,
        'avail_end': 675
    }
    friends_all = [barbara, betty, david]
    
    itinerary = None
    # Try to meet all three friends
    itinerary = schedule_k_friends(friends_all, travel_matrix, location_to_index)
    if itinerary is not None:
        print(f'{{"itinerary": {itinerary}}}')
        return
        
    # Try all pairs of friends
    for two_friends in itertools.combinations(friends_all, 2):
        itinerary = schedule_k_friends(list(two_friends), travel_matrix, location_to_index)
        if itinerary is not None:
            print(f'{{"itinerary": {itinerary}}}')
            return
            
    # Try individual friends and choose the one that finishes earliest
    best_end_time = None
    best_meeting = None
    for friend in friends_all:
        loc_index = location_to_index[friend['location']]
        travel_time = travel_matrix[0][loc_index]
        s0 = max(travel_time, friend['avail_start'])
        end_time = s0 + friend['duration']
        if end_time > friend['avail_end']:
            continue
        if best_end_time is None or end_time < best_end_time:
            best_end_time = end_time
            best_meeting = {
                "action": "meet",
                "person": friend['name'],
                "start_time": min_to_time(s0),
                "end_time": min_to_time(end_time)
            }
    if best_meeting is not None:
        print(f'{{"itinerary": [{best_meeting}]}}')
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()