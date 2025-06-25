from z3 import *
import json

def main():
    stay_dict = {
        'Warsaw': 3,
        'Porto': 5,
        'Naples': 4,
        'Brussels': 3,
        'Split': 3,
        'Reykjavik': 5,
        'Amsterdam': 4,
        'Lyon': 3,
        'Helsinki': 4,
        'Valencia': 2
    }
    cities = list(stay_dict.keys())
    
    flight_edges_list = [
        ("Amsterdam", "Warsaw"),
        ("Helsinki", "Brussels"),
        ("Helsinki", "Warsaw"),
        ("Reykjavik", "Brussels"),
        ("Amsterdam", "Lyon"),
        ("Amsterdam", "Naples"),
        ("Amsterdam", "Reykjavik"),
        ("Naples", "Valencia"),
        ("Porto", "Brussels"),
        ("Amsterdam", "Split"),
        ("Lyon", "Split"),
        ("Warsaw", "Split"),
        ("Porto", "Amsterdam"),
        ("Helsinki", "Split"),
        ("Brussels", "Lyon"),
        ("Porto", "Lyon"),
        ("Reykjavik", "Warsaw"),
        ("Brussels", "Valencia"),
        ("Valencia", "Lyon"),
        ("Porto", "Warsaw"),
        ("Warsaw", "Valencia"),
        ("Amsterdam", "Helsinki"),
        ("Porto", "Valencia"),
        ("Warsaw", "Brussels"),
        ("Warsaw", "Naples"),
        ("Naples", "Split"),
        ("Helsinki", "Naples"),
        ("Helsinki", "Reykjavik"),
        ("Amsterdam", "Valencia"),
        ("Naples", "Brussels")
    ]
    
    normalized_flight_set = set()
    for a, b in flight_edges_list:
        normalized_flight_set.add((min(a, b), max(a, b)))
    
    pos = {c: Int(f'pos_{c}') for c in cities}
    s = Solver()
    
    for c in cities:
        s.add(pos[c] >= 0, pos[c] <= 9)
    s.add(Distinct([pos[c] for c in cities]))
    
    start = {}
    for c in cities:
        sum_before = 0
        for d in cities:
            if d == c:
                continue
            sum_before += If(pos[d] < pos[c], stay_dict[d], 0)
        start[c] = 1 + sum_before - pos[c]
    
    s.add(start['Naples'] == 17)
    s.add(start['Brussels'] == 20)
    s.add(start['Porto'] <= 5)
    s.add(start['Amsterdam'] >= 2, start['Amsterdam'] <= 8)
    s.add(start['Helsinki'] >= 5, start['Helsinki'] <= 11)
    
    for i in range(len(cities)):
        for j in range(i+1, len(cities)):
            c1 = cities[i]
            c2 = cities[j]
            pair = (min(c1, c2), max(c1, c2))
            if pair not in normalized_flight_set:
                s.add(Not(Or(pos[c1] - pos[c2] == 1, pos[c1] - pos[c2] == -1)))
    
    if s.check() == sat:
        m = s.model()
        pos_val = {}
        for c in cities:
            pos_val[c] = m.evaluate(pos[c]).as_long()
        
        order_sorted = sorted(cities, key=lambda c: pos_val[c])
        
        itinerary = []
        current_day = 1
        for idx, city in enumerate(order_sorted):
            start_city = current_day
            end_city = start_city + stay_dict[city] - 1
            itinerary.append({"day_range": f"Day {start_city}-{end_city}", "place": city})
            
            if idx < len(cities) - 1:
                next_city = order_sorted[idx+1]
                itinerary.append({"day_range": f"Day {end_city}", "place": city})
                itinerary.append({"day_range": f"Day {end_city}", "place": next_city})
                current_day = end_city
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()