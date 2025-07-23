from z3 import *
import json

def main():
    # Define the city enum
    CitySort, city_con = EnumSort('City', [
        'Istanbul', 
        'Brussels', 
        'Helsinki', 
        'Split', 
        'Dubrovnik', 
        'Milan', 
        'Vilnius', 
        'Frankfurt'
    ])
    Istanbul, Brussels, Helsinki, Split, Dubrovnik, Milan, Vilnius, Frankfurt = city_con
    city_dict = {
        'Istanbul': Istanbul,
        'Brussels': Brussels,
        'Helsinki': Helsinki,
        'Split': Split,
        'Dubrovnik': Dubrovnik,
        'Milan': Milan,
        'Vilnius': Vilnius,
        'Frankfurt': Frankfurt
    }
    
    # Arrays for start and end cities for each day
    start = [None]  # index 0 unused
    end = [None]
    for i in range(1, 23):
        start.append(Const('start_%d' % i, CitySort))
        end.append(Const('end_%d' % i, CitySort))
    
    s = Solver()
    
    # Constraint: end of day d must equal start of day d+1
    for d in range(1, 22):
        s.add(end[d] == start[d+1])
    
    # Fixed start and end
    s.add(start[1] == Istanbul)
    s.add(end[22] == Vilnius)
    
    # Fixed periods
    # Istanbul: days 1-5
    for d in range(1, 6):
        s.add(Or(start[d] == Istanbul, end[d] == Istanbul))
    
    # Vilnius: days 18-22
    for d in range(18, 23):
        s.add(Or(start[d] == Vilnius, end[d] == Vilnius))
    
    # Frankfurt: days 16,17,18
    for d in [16, 17, 18]:
        s.add(Or(start[d] == Frankfurt, end[d] == Frankfurt))
    
    # Define direct flight connections
    directed_edges = []
    bidirectional_pairs = [
        ('Milan', 'Frankfurt'),
        ('Split', 'Frankfurt'),
        ('Milan', 'Split'),
        ('Brussels', 'Vilnius'),
        ('Brussels', 'Helsinki'),
        ('Istanbul', 'Brussels'),
        ('Milan', 'Vilnius'),
        ('Brussels', 'Milan'),
        ('Istanbul', 'Helsinki'),
        ('Helsinki', 'Vilnius'),
        ('Helsinki', 'Dubrovnik'),
        ('Split', 'Vilnius'),
        ('Istanbul', 'Milan'),
        ('Helsinki', 'Frankfurt'),
        ('Istanbul', 'Vilnius'),
        ('Split', 'Helsinki'),
        ('Milan', 'Helsinki'),
        ('Istanbul', 'Frankfurt'),
        ('Dubrovnik', 'Frankfurt'),
        ('Frankfurt', 'Vilnius')
    ]
    for a, b in bidirectional_pairs:
        directed_edges.append((a, b))
        directed_edges.append((b, a))
    directed_edges.append(('Dubrovnik', 'Istanbul'))
    directed_edges.append(('Brussels', 'Frankfurt'))
    
    # Flight constraints: if start and end differ, must be a direct flight
    for d in range(1, 23):
        conds = []
        for a, b in directed_edges:
            conds.append(And(start[d] == city_dict[a], end[d] == city_dict[b]))
        s.add(If(start[d] != end[d], Or(conds), True))
    
    # Total days per city
    req_days = {
        'Istanbul': 5,
        'Brussels': 3,
        'Helsinki': 3,
        'Split': 4,
        'Dubrovnik': 2,
        'Milan': 4,
        'Vilnius': 5,
        'Frankfurt': 3
    }
    for city_name, days_req in req_days.items():
        total = 0
        c = city_dict[city_name]
        for d in range(1, 23):
            total += If(Or(start[d] == c, end[d] == c), 1, 0)
        s.add(total == days_req)
    
    # Solve and output
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for d in range(1, 23):
            s_val = model[start[d]]
            s_name = s_val.decl().name()
            itinerary.append({"day": d, "place": s_name})
            e_val = model[end[d]]
            e_name = e_val.decl().name()
            if s_val != e_val:
                itinerary.append({"day": d, "place": e_name})
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()