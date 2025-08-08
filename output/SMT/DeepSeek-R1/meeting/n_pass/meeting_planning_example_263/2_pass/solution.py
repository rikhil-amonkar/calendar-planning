import itertools
import json

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def main():
    friends = [
        {'name': 'Karen', 'loc': "Fisherman's Wharf", 'duration': 30, 'min_start': 8*60+45, 'max_end': 15*60},
        {'name': 'Anthony', 'loc': "Financial District", 'duration': 105, 'min_start': 9*60+15, 'max_end': 21*60+30},
        {'name': 'Betty', 'loc': "Embarcadero", 'duration': 15, 'min_start': 19*60+45, 'max_end': 21*60+45}
    ]
    
    travel_from_bayview = {
        "Fisherman's Wharf": 25,
        "Financial District": 19,
        "Embarcadero": 19
    }
    
    travel_between = {
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Embarcadero"): 4,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Financial District"): 5
    }
    
    permutations = list(itertools.permutations([0, 1, 2]))
    
    for perm in permutations:
        a, b, c = perm
        f1 = friends[a]
        f2 = friends[b]
        f3 = friends[c]
        
        s1 = max(540 + travel_from_bayview[f1['loc']], f1['min_start'])
        if s1 + f1['duration'] > f1['max_end']:
            continue
            
        travel1 = travel_between[(f1['loc'], f2['loc'])]
        s2 = max(s1 + f1['duration'] + travel1, f2['min_start'])
        if s2 + f2['duration'] > f2['max_end']:
            continue
            
        travel2 = travel_between[(f2['loc'], f3['loc'])]
        s3 = max(s2 + f2['duration'] + travel2, f3['min_start'])
        if s3 + f3['duration'] > f3['max_end']:
            continue
            
        meetings_list = [
            {'person': f1['name'], 'start': s1, 'end': s1 + f1['duration']},
            {'person': f2['name'], 'start': s2, 'end': s2 + f2['duration']},
            {'person': f3['name'], 'start': s3, 'end': s3 + f3['duration']}
        ]
        meetings_list.sort(key=lambda x: x['start'])
        itinerary = []
        for meet in meetings_list:
            itinerary.append({
                "action": "meet",
                "person": meet['person'],
                "start_time": minutes_to_time(meet['start']),
                "end_time": minutes_to_time(meet['end'])
            })
        print(f'{{"itinerary": {json.dumps(itinerary)}}}')
        return
    
    pairs = [(0,1), (0,2), (1,2)]
    for pair in pairs:
        for order in [0,1]:
            if order == 0:
                i, j = pair
            else:
                j, i = pair
            f1 = friends[i]
            f2 = friends[j]
            
            s1 = max(540 + travel_from_bayview[f1['loc']], f1['min_start'])
            if s1 + f1['duration'] > f1['max_end']:
                continue
                
            travel_time = travel_between[(f1['loc'], f2['loc'])]
            s2 = max(s1 + f1['duration'] + travel_time, f2['min_start'])
            if s2 + f2['duration'] > f2['max_end']:
                continue
                
            meetings_list = [
                {'person': f1['name'], 'start': s1, 'end': s1 + f1['duration']},
                {'person': f2['name'], 'start': s2, 'end': s2 + f2['duration']}
            ]
            meetings_list.sort(key=lambda x: x['start'])
            itinerary = []
            for meet in meetings_list:
                itinerary.append({
                    "action": "meet",
                    "person": meet['person'],
                    "start_time": minutes_to_time(meet['start']),
                    "end_time": minutes_to_time(meet['end'])
                })
            print(f'{{"itinerary": {json.dumps(itinerary)}}}')
            return
            
    for i in range(3):
        friend = friends[i]
        s = max(540 + travel_from_bayview[friend['loc']], friend['min_start'])
        if s + friend['duration'] <= friend['max_end']:
            itinerary = [{
                "action": "meet",
                "person": friend['name'],
                "start_time": minutes_to_time(s),
                "end_time": minutes_to_time(s + friend['duration'])
            }]
            print(f'{{"itinerary": {json.dumps(itinerary)}}}')
            return
            
    print('{"itinerary": []}')

if __name__ == '__main__':
    main()