from z3 import *

def main():
    City, cities = EnumSort('City', [
        'Oslo',
        'Helsinki',
        'Edinburgh',
        'Riga',
        'Tallinn',
        'Budapest',
        'Vilnius',
        'Porto',
        'Geneva'
    ])
    Oslo, Helsinki, Edinburgh, Riga, Tallinn, Budapest, Vilnius, Porto, Geneva = cities
    city_list = [Oslo, Helsinki, Edinburgh, Riga, Tallinn, Budapest, Vilnius, Porto, Geneva]
    city_names = ['Oslo', 'Helsinki', 'Edinburgh', 'Riga', 'Tallinn', 'Budapest', 'Vilnius', 'Porto', 'Geneva']
    
    req_map = {
        Oslo: 2,
        Helsinki: 2,
        Edinburgh: 3,
        Riga: 2,
        Tallinn: 5,
        Budapest: 5,
        Vilnius: 5,
        Porto: 5,
        Geneva: 4
    }
    
    allowed_edges = []
    bidirs = [
        (Porto, Oslo),
        (Edinburgh, Budapest),
        (Edinburgh, Geneva),
        (Edinburgh, Porto),
        (Vilnius, Helsinki),
        (Riga, Oslo),
        (Geneva, Oslo),
        (Edinburgh, Oslo),
        (Edinburgh, Helsinki),
        (Vilnius, Oslo),
        (Riga, Helsinki),
        (Budapest, Geneva),
        (Helsinki, Budapest),
        (Helsinki, Oslo),
        (Edinburgh, Riga),
        (Tallinn, Helsinki),
        (Geneva, Porto),
        (Tallinn, Oslo),
        (Budapest, Oslo),
        (Helsinki, Geneva)
    ]
    for (a, b) in bidirs:
        allowed_edges.append((a, b))
        allowed_edges.append((b, a))
    
    directs = [
        (Riga, Tallinn),
        (Tallinn, Vilnius),
        (Riga, Vilnius)
    ]
    for (a, b) in directs:
        allowed_edges.append((a, b))
    
    x = [Const('x' + str(i), City) for i in range(26)]
    s = Solver()
    
    for d in range(1, 26):
        a = x[d-1]
        b = x[d]
        or_conditions = [a == b]
        for edge in allowed_edges:
            a_edge, b_edge = edge
            or_conditions.append(And(a == a_edge, b == b_edge))
        s.add(Or(or_conditions))
    
    for city in city_list:
        total = 0
        for d in range(1, 26):
            total += If(Or(x[d-1] == city, x[d] == city), 1, 0)
        s.add(total == req_map[city])
    
    s.add(Or(x[23] == Oslo, x[24] == Oslo, x[25] == Oslo))
    
    full_day_in_Tallinn = []
    for d in range(4, 9):
        full_day_in_Tallinn.append(And(x[d-1] == Tallinn, x[d] == Tallinn))
    s.add(Or(full_day_in_Tallinn))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(1, 26):
            start_city = m.eval(x[day-1])
            end_city = m.eval(x[day])
            start_city_str = str(start_city)
            end_city_str = str(end_city)
            if start_city_str == end_city_str:
                cities_on_day = [start_city_str]
            else:
                cities_on_day = [start_city_str, end_city_str]
            itinerary.append({"day": day, "city": cities_on_day})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()