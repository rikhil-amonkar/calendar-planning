from z3 import *
import json

def main():
    City, cities_enum = EnumSort('City', ['Dublin', 'Krakow', 'Istanbul', 'Venice', 'Naples', 'Brussels', 'Mykonos', 'Frankfurt'])
    Dublin, Krakow, Istanbul, Venice, Naples, Brussels, Mykonos, Frankfurt = cities_enum

    city_map = {
        'Dublin': Dublin,
        'Krakow': Krakow,
        'Istanbul': Istanbul,
        'Venice': Venice,
        'Naples': Naples,
        'Brussels': Brussels,
        'Mykonos': Mykonos,
        'Frankfurt': Frankfurt
    }

    bidirectional_phrases = [
        "Dublin and Brussels",
        "Mykonos and Naples",
        "Venice and Istanbul",
        "Frankfurt and Krakow",
        "Naples and Dublin",
        "Krakow and Brussels",
        "Naples and Istanbul",
        "Naples and Brussels",
        "Istanbul and Frankfurt",
        "Istanbul and Krakow",
        "Istanbul and Brussels",
        "Venice and Frankfurt",
        "Naples and Frankfurt",
        "Dublin and Krakow",
        "Venice and Brussels",
        "Naples and Venice",
        "Istanbul and Dublin",
        "Venice and Dublin",
        "Dublin and Frankfurt"
    ]

    directed_phrases = [
        "from Brussels to Frankfurt"
    ]

    directed_edges = []
    for phrase in bidirectional_phrases:
        parts = phrase.split(' and ')
        A_str = parts[0].strip()
        B_str = parts[1].strip()
        A = city_map[A_str]
        B = city_map[B_str]
        directed_edges.append((A, B))
        directed_edges.append((B, A))
    
    for phrase in directed_phrases:
        parts = phrase.split()
        A_str = parts[1].strip()
        B_str = parts[3].strip()
        A = city_map[A_str]
        B = city_map[B_str]
        directed_edges.append((A, B))

    s0 = Const('s0', City)
    x = [Const('x_%d' % i, City) for i in range(21)]
    s = Solver()

    # Flight constraint for initial move (s0 to day1)
    if directed_edges:
        flight_edges = [ And(s0 == a, x[0] == b) for (a,b) in directed_edges ]
        s.add(Implies(s0 != x[0], Or(flight_edges)))
    else:
        s.add(True)

    # Flight constraints between consecutive days
    for i in range(1, 21):
        if directed_edges:
            flight_edges = [ And(x[i-1] == a, x[i] == b) for (a,b) in directed_edges ]
            s.add(Implies(x[i-1] != x[i], Or(flight_edges)))
        else:
            s.add(True)

    # Calculate presence in city on given day
    def presence(c, d):
        if d == 1:
            return Or(s0 == c, x[0] == c)
        else:
            idx_start = d - 2
            idx_end = d - 1
            return Or(x[idx_start] == c, x[idx_end] == c)

    # Total days constraints
    total_days_dict = {
        Dublin: 5,
        Krakow: 4,
        Istanbul: 3,
        Venice: 3,
        Naples: 4,
        Brussels: 2,
        Mykonos: 4,
        Frankfurt: 3
    }

    for city, total_req in total_days_dict.items():
        total = 0
        for d in range(1, 22):
            total += If(presence(city, d), 1, 0)
        s.add(total == total_req)

    # Specific date constraints - REVISED for Dublin to ensure full presence
    # Enforce being in Dublin at the end of days 11,12,13,14 (ensures full days 11-15)
    s.add(x[10] == Dublin)  # End of day 11
    s.add(x[11] == Dublin)  # End of day 12
    s.add(x[12] == Dublin)  # End of day 13
    s.add(x[13] == Dublin)  # End of day 14

    # Other event constraints remain the same
    s.add(Or([presence(Istanbul, d) for d in [9,10,11]]))
    s.add(Or([presence(Mykonos, d) for d in [1,2,3,4]]))
    s.add(Or([presence(Frankfurt, d) for d in [15,16,17]]))

    if s.check() == sat:
        m = s.model()
        s0_val = m[s0]
        x_vals = [m[var] for var in x]
        city_names = {
            Dublin: 'Dublin',
            Krakow: 'Krakow',
            Istanbul: 'Istanbul',
            Venice: 'Venice',
            Naples: 'Naples',
            Brussels: 'Brussels',
            Mykonos: 'Mykonos',
            Frankfurt: 'Frankfurt'
        }
        itinerary_list = []
        for day in range(1, 22):
            if day == 1:
                city_val = x_vals[0]
            else:
                city_val = x_vals[day-1]
            city_name = city_names[city_val]
            itinerary_list.append({"day": day, "place": city_name})
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()