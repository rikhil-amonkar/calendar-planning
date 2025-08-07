from z3 import *

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def main():
    meetings = [
        {"name": "Karen", "location": "Fisherman's Wharf", "duration": 30, "min_start": 8*60+45, "max_end": 15*60},
        {"name": "Anthony", "location": "Financial District", "duration": 105, "min_start": 9*60+15, "max_end": 21*60+30},
        {"name": "Betty", "location": "Embarcadero", "duration": 15, "min_start": 19*60+45, "max_end": 21*60+45}
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
    
    s = Solver()
    
    first = Int('first')
    second = Int('second')
    third = Int('third')
    
    s0 = Int('s0')
    s1 = Int('s1')
    s2 = Int('s2')
    
    s_k = Int('s_k')
    s_a = Int('s_a')
    s_b = Int('s_b')
    
    s.add(Distinct(first, second, third))
    s.add(first >= 0, first <= 2)
    s.add(second >= 0, second <= 2)
    s.add(third >= 0, third <= 2)
    
    s.add(s0 == 540 + travel_from_bayview[meetings[first]["location"]])
    s.add(s1 == s0 + meetings[first]["duration"] + travel_between[(meetings[first]["location"], meetings[second]["location"])])
    s.add(s2 == s1 + meetings[second]["duration"] + travel_between[(meetings[second]["location"], meetings[third]["location"])])
    
    s.add(s_k == If(first == 0, s0, If(second == 0, s1, s2)))
    s.add(s_a == If(first == 1, s0, If(second == 1, s1, s2)))
    s.add(s_b == If(first == 2, s0, If(second == 2, s1, s2)))
    
    s.add(s_k >= meetings[0]["min_start"], s_k + meetings[0]["duration"] <= meetings[0]["max_end"])
    s.add(s_a >= meetings[1]["min_start"], s_a + meetings[1]["duration"] <= meetings[1]["max_end"])
    s.add(s_b >= meetings[2]["min_start"], s_b + meetings[2]["duration"] <= meetings[2]["max_end"])
    
    if s.check() == sat:
        m = s.model()
        s_k_val = m.eval(s_k).as_long()
        s_a_val = m.eval(s_a).as_long()
        s_b_val = m.eval(s_b).as_long()
        meetings_list = [
            {"person": "Karen", "start": s_k_val, "end": s_k_val + 30},
            {"person": "Anthony", "start": s_a_val, "end": s_a_val + 105},
            {"person": "Betty", "start": s_b_val, "end": s_b_val + 15}
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
    
    pairs = [
        (0, 1), 
        (0, 2), 
        (1, 2)
    ]
    orders = [(0, 1), (1, 0)]
    
    for pair in pairs:
        for order in orders:
            idx1 = pair[order[0]]
            idx2 = pair[order[1]]
            loc1 = meetings[idx1]["location"]
            loc2 = meetings[idx2]["location"]
            travel_time = travel_between[(loc1, loc2)]
            
            start1 = 540 + travel_from_bayview[loc1]
            end1 = start1 + meetings[idx1]["duration"]
            start2 = end1 + travel_time
            end2 = start2 + meetings[idx2]["duration"]
            
            valid = True
            if start1 < meetings[idx1]["min_start"] or end1 > meetings[idx1]["max_end"]:
                valid = False
            if start2 < meetings[idx2]["min_start"] or end2 > meetings[idx2]["max_end"]:
                valid = False
                
            if valid:
                meetings_list = [
                    {"person": meetings[idx1]["name"], "start": start1, "end": end1},
                    {"person": meetings[idx2]["name"], "start": start2, "end": end2}
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
    
    for idx in range(3):
        start = 540 + travel_from_bayview[meetings[idx]["location"]]
        end = start + meetings[idx]["duration"]
        if start >= meetings[idx]["min_start"] and end <= meetings[idx]["max_end"]:
            itinerary = [{
                "action": "meet",
                "person": meetings[idx]["name"],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            }]
            print(f'{{"itinerary": {json.dumps(itinerary)}}}')
            return
    
    print('{"itinerary": []}')

if __name__ == '__main__':
    import json
    main()