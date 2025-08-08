from z3 import *
import json

def main():
    cities = ["Brussels", "Helsinki", "Split", "Dubrovnik", "Istanbul", "Milan", "Vilnius", "Frankfurt"]
    
    directed_edges = []
    directed_edges.append(("Dubrovnik", "Istanbul"))
    directed_edges.append(("Brussels", "Frankfurt"))
    
    bidirectional_edges = [
        ("Milan", "Frankfurt"),
        ("Split", "Frankfurt"),
        ("Milan", "Split"),
        ("Brussels", "Vilnius"),
        ("Brussels", "Helsinki"),
        ("Istanbul", "Brussels"),
        ("Milan", "Vilnius"),
        ("Brussels", "Milan"),
        ("Istanbul", "Helsinki"),
        ("Helsinki", "Vilnius"),
        ("Helsinki", "Dubrovnik"),
        ("Split", "Vilnius"),
        ("Istanbul", "Milan"),
        ("Helsinki", "Frankfurt"),
        ("Istanbul", "Vilnius"),
        ("Split", "Helsinki"),
        ("Milan", "Helsinki"),
        ("Istanbul", "Frankfurt"),
        ("Dubrovnik", "Frankfurt"),
        ("Frankfurt", "Vilnius")
    ]
    
    for a, b in bidirectional_edges:
        directed_edges.append((a, b))
        directed_edges.append((b, a))
    
    allowed_edges = set(directed_edges)
    
    CitySort, city_consts = EnumSort('City', cities)
    Brussels, Helsinki, Split, Dubrovnik, Istanbul, Milan, Vilnius, Frankfurt = city_consts
    
    city_map = {
        "Brussels": Brussels,
        "Helsinki": Helsinki,
        "Split": Split,
        "Dubrovnik": Dubrovnik,
        "Istanbul": Istanbul,
        "Milan": Milan,
        "Vilnius": Vilnius,
        "Frankfurt": Frankfurt
    }
    
    rev_map = dict(zip(city_consts, cities))
    
    nights = [Const('night_%d' % i, CitySort) for i in range(23)]
    s = Solver()
    
    s.add(nights[0] == Istanbul)
    
    for d in range(1, 23):
        from_city = nights[d-1]
        to_city = nights[d]
        s.add(If(from_city == to_city, True, Or([And(from_city == city_map[a], to_city == city_map[b]) for (a, b) in allowed_edges)))
    
    for d in range(1, 6):
        s.add(Or(nights[d-1] == Istanbul, nights[d] == Istanbul))
    
    for d in range(18, 23):
        s.add(Or(nights[d-1] == Vilnius, nights[d] == Vilnius))
    
    frankfurt_days = []
    for d in range(16, 19):
        frankfurt_days.append(Or(nights[d-1] == Frankfurt, nights[d] == Frankfurt))
    s.add(Or(frankfurt_days))
    
    total_days = {}
    for c in cities:
        total_days[c] = Int(f'total_days_{c}')
        days_list = []
        for d in range(1, 23):
            cond = Or(nights[d-1] == city_map[c], nights[d] == city_map[c])
            days_list.append(If(cond, 1, 0))
        s.add(total_days[c] == Sum(days_list))
    
    s.add(total_days["Brussels"] == 3)
    s.add(total_days["Helsinki"] == 3)
    s.add(total_days["Split"] == 4)
    s.add(total_days["Dubrovnik"] == 2)
    s.add(total_days["Istanbul"] == 5)
    s.add(total_days["Milan"] == 4)
    s.add(total_days["Vilnius"] == 5)
    s.add(total_days["Frankfurt"] == 3)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for d in range(1, 23):
            n_val = m.evaluate(nights[d])
            city_name = rev_map[n_val]
            itinerary.append({"day": d, "place": city_name})
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()