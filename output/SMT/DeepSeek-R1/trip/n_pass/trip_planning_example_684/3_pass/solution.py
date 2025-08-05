from z3 import *
import json

def main():
    City, (Amsterdam, Edinburgh, Brussels, Vienna, Berlin, Reykjavik) = EnumSort('City', 
        ['Amsterdam', 'Edinburgh', 'Brussels', 'Vienna', 'Berlin', 'Reykjavik'])
    cities = [Amsterdam, Edinburgh, Brussels, Vienna, Berlin, Reykjavik]
    city_names = {
        Amsterdam: 'Amsterdam',
        Edinburgh: 'Edinburgh',
        Brussels: 'Brussels',
        Vienna: 'Vienna',
        Berlin: 'Berlin',
        Reykjavik: 'Reykjavik'
    }
    
    required_days = {
        Amsterdam: 4,
        Edinburgh: 5,
        Brussels: 5,
        Vienna: 5,
        Berlin: 4,
        Reykjavik: 5
    }
    
    direct_flights = [
        ("Edinburgh", "Berlin"), ("Amsterdam", "Berlin"), ("Edinburgh", "Amsterdam"), 
        ("Vienna", "Berlin"), ("Berlin", "Brussels"), ("Vienna", "Reykjavik"), 
        ("Edinburgh", "Brussels"), ("Vienna", "Brussels"), ("Amsterdam", "Reykjavik"), 
        ("Reykjavik", "Brussels"), ("Amsterdam", "Vienna"), ("Reykjavik", "Berlin")
    ]
    allowed_pairs = []
    for a_str, b_str in direct_flights:
        a_city = None
        b_city = None
        for c in cities:
            if city_names[c] == a_str:
                a_city = c
            if city_names[c] == b_str:
                b_city = c
        if a_city is not None and b_city is not None:
            allowed_pairs.append((a_city, b_city))
            allowed_pairs.append((b_city, a_city))
    
    n_days = 23
    s0 = Const('s0', City)
    c = [Const('c_%d' % i, City) for i in range(n_days)]
    
    s = Solver()
    
    s.add(Or(s0 == c[0], Or([And(s0 == a, c[0] == b) for (a, b) in allowed_pairs])))
    
    for i in range(n_days - 1):
        same_city = c[i] == c[i+1]
        valid_flight = Or([And(c[i] == a, c[i+1] == b) for (a, b) in allowed_pairs])
        s.add(Or(same_city, valid_flight))
    
    for city in cities:
        total = 0
        for j in range(n_days):
            if j == 0:
                cond = Or(s0 == city, c[0] == city)
            else:
                cond = Or(c[j-1] == city, c[j] == city)
            total += If(cond, 1, 0)
        s.add(total == required_days[city])
    
    # Amsterdam must be visited between days 5-8
    ams_constraints = []
    for day in [5, 6, 7, 8]:
        if day == 1:
            ams_constraints.append(Or(s0 == Amsterdam, c[0] == Amsterdam))
        else:
            ams_constraints.append(Or(c[day-2] == Amsterdam, c[day-1] == Amsterdam))
    s.add(Or(ams_constraints))
    
    # Berlin must be visited between days 16-19
    ber_constraints = []
    for day in [16, 17, 18, 19]:
        if day == 1:
            ber_constraints.append(Or(s0 == Berlin, c[0] == Berlin))
        else:
            ber_constraints.append(Or(c[day-2] == Berlin, c[day-1] == Berlin))
    s.add(Or(ber_constraints))
    
    # Reykjavik must be visited between days 12-16
    rek_constraints = []
    for day in [12, 13, 14, 15, 16]:
        if day == 1:
            rek_constraints.append(Or(s0 == Reykjavik, c[0] == Reykjavik))
        else:
            rek_constraints.append(Or(c[day-2] == Reykjavik, c[day-1] == Reykjavik))
    s.add(Or(rek_constraints))
    
    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        current_city = None
        start_day = 1
        for i in range(n_days):
            city_val = m.eval(c[i])
            city_name = city_names[city_val]
            if city_name != current_city:
                if current_city is not None:
                    itinerary_list.append({
                        "day_range": f"Day {start_day}-{i}",
                        "place": current_city
                    })
                current_city = city_name
                start_day = i+1
        itinerary_list.append({
            "day_range": f"Day {start_day}-{n_days}",
            "place": current_city
        })
        print(json.dumps({"itinerary": itinerary_list}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()