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

    x = [Const('x_%d' % i, City) for i in range(21)]
    s = Solver()

    for i in range(1, 21):
        stay = (x[i] == x[i-1])
        moves = []
        for (A, B) in directed_edges:
            moves.append(And(x[i-1] == A, x[i] == B))
        s.add(Or(stay, Or(moves)))
    
    def total_days(city):
        total = If(x[0] == city, 1, 0)
        for j in range(2, 22):
            idx_start = j - 2
            idx_end = j - 1
            cond = Or(x[idx_start] == city, x[idx_end] == city)
            total = total + If(cond, 1, 0)
        return total

    s.add(total_days(Dublin) == 5)
    s.add(total_days(Krakow) == 4)
    s.add(total_days(Istanbul) == 3)
    s.add(total_days(Venice) == 3)
    s.add(total_days(Naples) == 4)
    s.add(total_days(Brussels) == 2)
    s.add(total_days(Mykonos) == 4)
    s.add(total_days(Frankfurt) == 3)

    dublin_constraints = []
    for day in [11, 12, 13, 14, 15]:
        if day == 1:
            cond = (x[0] == Dublin)
        else:
            idx1 = day - 2
            idx2 = day - 1
            cond = Or(x[idx1] == Dublin, x[idx2] == Dublin)
        dublin_constraints.append(cond)
    s.add(And(dublin_constraints))

    istanbul_constraints = []
    for day in [9, 10, 11]:
        if day == 1:
            cond = (x[0] == Istanbul)
        else:
            idx1 = day - 2
            idx2 = day - 1
            cond = Or(x[idx1] == Istanbul, x[idx2] == Istanbul)
        istanbul_constraints.append(cond)
    s.add(Or(istanbul_constraints))

    mykonos_constraints = []
    for day in [1, 2, 3, 4]:
        if day == 1:
            cond = (x[0] == Mykonos)
        else:
            idx1 = day - 2
            idx2 = day - 1
            cond = Or(x[idx1] == Mykonos, x[idx2] == Mykonos)
        mykonos_constraints.append(cond)
    s.add(Or(mykonos_constraints))

    frankfurt_constraints = []
    for day in [15, 16, 17]:
        idx1 = day - 2
        idx2 = day - 1
        cond = Or(x[idx1] == Frankfurt, x[idx2] == Frankfurt)
        frankfurt_constraints.append(cond)
    s.add(Or(frankfurt_constraints))

    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for i in range(21):
            city_val = m[x[i]]
            city_name = city_val.decl().name()
            itinerary_list.append({"day": i+1, "place": city_name})
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()