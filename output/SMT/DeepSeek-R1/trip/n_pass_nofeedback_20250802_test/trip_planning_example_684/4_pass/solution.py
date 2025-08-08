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
    c = [Const('c_%d' % i, City) for i in range(n_days)]
    
    s = Solver()
    
    # Flight constraints between consecutive days
    for i in range(n_days - 1):
        same_city = c[i] == c[i+1]
        valid_flight = Or([And(c[i] == a, c[i+1] == b) for (a, b) in allowed_pairs])
        s.add(Or(same_city, valid_flight))
    
    # Total days per city constraint
    for city in cities:
        total = Sum([If(c[i] == city, 1, 0) for i in range(n_days)])
        s.add(total == required_days[city])
    
    # Amsterdam must be visited between days 5-8 (1-indexed days 5,6,7,8)
    ams_constraint = Or([c[i] == Amsterdam for i in [4,5,6,7]])  # indices 4-7 = days 5-8
    s.add(ams_constraint)
    
    # Berlin must be visited between days 16-19 (1-indexed days 16,17,18,19)
    ber_constraint = Or([c[i] == Berlin for i in [15,16,17,18]])  # indices 15-18 = days 16-19
    s.add(ber_constraint)
    
    # Reykjavik must be visited between days 12-16 (1-indexed days 12,13,14,15,16)
    rek_constraint = Or([c[i] == Reykjavik for i in [11,12,13,14,15]])  # indices 11-15 = days 12-16
    s.add(rek_constraint)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current_city = None
        start_day = 1
        day_list = [city_names[m.eval(c[i])] for i in range(n_days)]
        
        for i in range(n_days):
            if day_list[i] != current_city:
                if current_city is not None:
                    itinerary.append({
                        "day_range": f"Day {start_day}-{i}",
                        "place": current_city
                    })
                current_city = day_list[i]
                start_day = i+1
        itinerary.append({
            "day_range": f"Day {start_day}-{n_days}",
            "place": current_city
        })
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()