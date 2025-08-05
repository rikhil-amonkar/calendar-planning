from z3 import *
import json

def main():
    n_days = 17
    cities = ['Naples', 'Vienna', 'Vilnius']
    
    # Create Z3 variables
    L = [Int('L_%d' % i) for i in range(n_days)]
    Fly = [Bool('Fly_%d' % i) for i in range(n_days-1)]
    
    s = Solver()
    
    # Initial location: Naples on day 1
    s.add(L[0] == 0)
    
    # Each L[i] must be 0, 1, or 2
    for i in range(n_days):
        s.add(L[i] >= 0, L[i] <= 2)
    
    # Flight constraints: flights only between connected cities
    for i in range(n_days-1):
        s.add(If(Fly[i],
                 Or(
                    And(L[i] == 0, L[i+1] == 1),
                    And(L[i] == 1, Or(L[i+1] == 0, L[i+1] == 2)),
                    And(L[i] == 2, L[i+1] == 1)
                 ),
                 L[i+1] == L[i]
                ))
    
    # Must be in Naples on days 1 to 5
    for day_index in range(5):
        if day_index < n_days-1:
            s.add(If(Fly[day_index],
                     Or(L[day_index] == 0, L[day_index+1] == 0),
                     L[day_index] == 0
                    ))
    
    # Total days in each city
    total_naples = 0
    total_vienna = 0
    total_vilnius = 0
    
    for day_index in range(n_days):
        if day_index < n_days-1:
            in_naples = If(Fly[day_index],
                           Or(L[day_index] == 0, L[day_index+1] == 0),
                           L[day_index] == 0)
            in_vienna = If(Fly[day_index],
                           Or(L[day_index] == 1, L[day_index+1] == 1),
                           L[day_index] == 1)
            in_vilnius = If(Fly[day_index],
                            Or(L[day_index] == 2, L[day_index+1] == 2),
                            L[day_index] == 2)
        else:
            in_naples = (L[day_index] == 0)
            in_vienna = (L[day_index] == 1)
            in_vilnius = (L[day_index] == 2)
            
        total_naples += If(in_naples, 1, 0)
        total_vienna += If(in_vienna, 1, 0)
        total_vilnius += If(in_vilnius, 1, 0)
    
    s.add(total_naples == 5)
    s.add(total_vienna == 7)
    s.add(total_vilnius == 7)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        for day_index in range(n_days-1):
            if is_true(m.evaluate(Fly[day_index])):
                city1 = m.evaluate(L[day_index])
                city2 = m.evaluate(L[day_index+1])
                itinerary.append({"day": day_index+1, "city": cities[city1.as_long()]})
                itinerary.append({"day": day_index+1, "city": cities[city2.as_long()]})
            else:
                city = m.evaluate(L[day_index])
                itinerary.append({"day": day_index+1, "city": cities[city.as_long()]})
        
        last_city = m.evaluate(L[n_days-1])
        itinerary.append({"day": n_days, "city": cities[last_city.as_long()]})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()