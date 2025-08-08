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
    
    def appear(city, day_index):
        return Or(x[day_index-1] == city, x[day_index] == city)
    
    for city in city_list:
        total = 0
        for d in range(1, 26):
            total += If(appear(city, d), 1, 0)
        s.add(total == req_map[city])
    
    for city in city_list:
        for i in range(1, 25):
            not_next_day = Not(appear(city, i+1))
            disappear_after = [Not(appear(city, j)) for j in range(i+2, 26)]
            s.add(Implies(And(appear(city, i), not_next_day), 
                         And(disappear_after) if disappear_after else True)
    
    s.add(Or(x[23] == Oslo, x[24] == Oslo, x[25] == Oslo))
    
    full_day_in_Tallinn = []
    for d in range(4, 9):
        full_day_in_Tallinn.append(And(x[d-1] == Tallinn, x[d] == Tallinn))
    s.add(Or(full_day_in_Tallinn))
    
    if s.check() == sat:
        m = s.model()
        segments = []
        day = 1
        while day <= 25:
            start_city = m.eval(x[day-1])
            end_city = m.eval(x[day])
            if start_city == end_city:
                j = day
                while j <= 25:
                    sc = m.eval(x[j-1])
                    ec = m.eval(x[j])
                    if sc == ec and sc == start_city:
                        j += 1
                    else:
                        break
                end_day = j - 1
                if day == end_day:
                    day_str = f"Day {day}"
                else:
                    day_str = f"Day {day}-{end_day}"
                segments.append({'day_range': day_str, 'place': str(start_city)})
                day = end_day + 1
            else:
                segments.append({'day_range': f"Day {day}", 'place': f"{str(start_city)}, {str(end_city)}"})
                day += 1
        
        result = {"itinerary": segments}
        print(f"Plan found: {result}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()