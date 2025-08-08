from z3 import *

def main():
    n_days = 16
    cities = ['Dubrovnik', 'Split', 'Milan', 'Porto', 'Krakow', 'Munich']
    
    city_day = [None] + [Const('city_day_%d' % i, StringSort()) for i in range(1, n_days+1)]
    flight_day = [None] + [Bool('flight_day_%d' % i) for i in range(1, n_days+1)]
    to_city = [None] + [Const('to_city_%d' % i, StringSort()) for i in range(1, n_days+1)]
    
    s = Solver()
    
    # Direct flights (both directions)
    direct_flights = [
        ('Munich', 'Porto'), ('Porto', 'Munich'),
        ('Split', 'Milan'), ('Milan', 'Split'),
        ('Milan', 'Porto'), ('Porto', 'Milan'),
        ('Munich', 'Krakow'), ('Krakow', 'Munich'),
        ('Munich', 'Milan'), ('Milan', 'Munich'),
        ('Dubrovnik', 'Munich'), ('Munich', 'Dubrovnik'),
        ('Krakow', 'Split'), ('Split', 'Krakow'),
        ('Krakow', 'Milan'), ('Milan', 'Krakow'),
        ('Munich', 'Split'), ('Split', 'Munich')
    ]
    
    # Start in one of the cities on day 1
    s.add(Or([city_day[1] == c for c in cities]))
    
    # Constraints for day transitions
    for d in range(1, n_days):
        s.add(If(flight_day[d], 
                 city_day[d+1] == to_city[d],
                 city_day[d+1] == city_day[d]))
    
    # No flight on the last day
    s.add(flight_day[16] == False)
    
    # Flight constraints: if flying, must be a direct flight
    for d in range(1, n_days+1):
        options = []
        for (c1, c2) in direct_flights:
            options.append(And(city_day[d] == c1, to_city[d] == c2))
        s.add(Implies(flight_day[d], Or(options)))
    
    # Munich must be present on days 4-8 and absent elsewhere
    for d in [4,5,6,7,8]:
        s.add(Or(city_day[d] == 'Munich', 
                 And(flight_day[d], to_city[d] == 'Munich')))
    for d in list(range(1,4)) + list(range(9,17)):
        s.add(Not(Or(city_day[d] == 'Munich', 
                     And(flight_day[d], to_city[d] == 'Munich'))))
    
    # Krakow must be present on days 8-9 and absent elsewhere
    for d in [8,9]:
        s.add(Or(city_day[d] == 'Krakow', 
                 And(flight_day[d], to_city[d] == 'Krakow')))
    for d in list(range(1,8)) + list(range(10,17)):
        s.add(Not(Or(city_day[d] == 'Krakow', 
                     And(flight_day[d], to_city[d] == 'Krakow'))))
    
    # Milan must be present on days 11-13 and absent elsewhere
    for d in [11,12,13]:
        s.add(Or(city_day[d] == 'Milan', 
                 And(flight_day[d], to_city[d] == 'Milan')))
    for d in list(range(1,11)) + [14,15,16]:
        s.add(Not(Or(city_day[d] == 'Milan', 
                     And(flight_day[d], to_city[d] == 'Milan'))))
    
    # Specific flight constraints
    s.add(flight_day[4] == True)
    s.add(to_city[4] == 'Munich')
    s.add(Or(city_day[4] == 'Dubrovnik', city_day[4] == 'Split', city_day[4] == 'Porto'))
    
    s.add(city_day[8] == 'Munich')
    s.add(flight_day[8] == True)
    s.add(to_city[8] == 'Krakow')
    
    s.add(flight_day[9] == True)
    s.add(Or(to_city[9] == 'Split', to_city[9] == 'Porto'))
    
    s.add(flight_day[13] == True)
    s.add(Or(to_city[13] == 'Split', to_city[13] == 'Porto'))
    
    # Total days per city
    counts = {}
    for c in cities:
        total = 0
        for d in range(1, n_days+1):
            cond = Or(city_day[d] == c, And(flight_day[d], to_city[d] == c))
            total += If(cond, 1, 0)
        counts[c] = total
        if c == 'Dubrovnik':
            s.add(total == 4)
        elif c == 'Split':
            s.add(total == 3)
        elif c == 'Milan':
            s.add(total == 3)
        elif c == 'Porto':
            s.add(total == 4)
        elif c == 'Krakow':
            s.add(total == 2)
        elif c == 'Munich':
            s.add(total == 5)
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for d in range(1, n_days+1):
            start_city = m.eval(city_day[d])
            itinerary.append({"day": d, "city": start_city.as_string()})
            if m.eval(flight_day[d]):
                dest_city = m.eval(to_city[d])
                itinerary.append({"day": d, "city": dest_city.as_string()})
        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()