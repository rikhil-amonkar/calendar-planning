from z3 import *
import json

def main():
    # Travel time matrix: 8x8 (index 0 to 7)
    # Locations: 
    # 0: Golden Gate Park
    # 1: Haight-Ashbury
    # 2: Fisherman's Wharf
    # 3: The Castro
    # 4: Chinatown
    # 5: Alamo Square
    # 6: North Beach
    # 7: Russian Hill
    T = [
        [0, 7, 24, 13, 23, 10, 24, 19],
        [7, 0, 23, 6, 19, 5, 19, 17],
        [25, 22, 0, 26, 12, 20, 6, 7],
        [11, 6, 24, 0, 20, 8, 20, 18],
        [23, 19, 8, 22, 0, 17, 3, 7],
        [9, 5, 19, 8, 16, 0, 15, 13],
        [22, 18, 5, 22, 6, 16, 0, 4],
        [21, 17, 7, 21, 9, 15, 5, 0]
    ]
    
    friends_data = [
        {'name': 'Carol', 'loc': 1, 'start_avail': 1290, 'end_avail': 1350, 'duration': 60},
        {'name': 'Laura', 'loc': 2, 'start_avail': 705, 'end_avail': 1290, 'duration': 60},
        {'name': 'Karen', 'loc': 3, 'start_avail': 435, 'end_avail': 840, 'duration': 75},
        {'name': 'Elizabeth', 'loc': 4, 'start_avail': 735, 'end_avail': 1290, 'duration': 75},
        {'name': 'Deborah', 'loc': 5, 'start_avail': 720, 'end_avail': 900, 'duration': 105},
        {'name': 'Jason', 'loc': 6, 'start_avail': 885, 'end_avail': 1140, 'duration': 90},
        {'name': 'Steven', 'loc': 7, 'start_avail': 885, 'end_avail': 1110, 'duration': 120}
    ]
    
    n = len(friends_data)
    meet = [Bool(f'meet_{i}') for i in range(n)]
    start = [Int(f'start_{i}') for i in range(n)]
    
    s = Optimize()
    
    # Constraints for each friend
    for i in range(n):
        loc_i = friends_data[i]['loc']
        s.add(Implies(meet[i], 
                      And(
                          start[i] >= 540 + T[0][loc_i],
                          start[i] >= friends_data[i]['start_avail'],
                          start[i] + friends_data[i]['duration'] <= friends_data[i]['end_avail']
                      )))
    
    # Constraints for pairs of friends
    before = {}
    for i in range(n):
        for j in range(i+1, n):
            b = Bool(f'b_{i}_{j}')
            before[(i, j)] = b
            loc_i = friends_data[i]['loc']
            loc_j = friends_data[j]['loc']
            s.add(Implies(And(meet[i], meet[j]),
                          Or(
                              And(b, start[i] + friends_data[i]['duration'] + T[loc_i][loc_j] <= start[j]),
                              And(Not(b), start[j] + friends_data[j]['duration'] + T[loc_j][loc_i] <= start[i])
                          )))
    
    # Maximize the number of meetings
    total_meet = Sum([If(meet[i], 1, 0) for i in range(n)])
    s.maximize(total_meet)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n):
            if m.eval(meet[i]):
                start_val = m.eval(start[i])
                if isinstance(start_val, IntNumRef):
                    start_min = start_val.as_long()
                else:
                    start_min = int(str(start_val))
                end_min = start_min + friends_data[i]['duration']
                # Convert minutes to HH:MM
                start_hour = start_min // 60
                start_minute = start_min % 60
                end_hour = end_min // 60
                end_minute = end_min % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friends_data[i]['name'],
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort by start time
        itinerary.sort(key=lambda x: x['start_time'])
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()