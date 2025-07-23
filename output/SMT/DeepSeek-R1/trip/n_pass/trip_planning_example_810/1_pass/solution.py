from z3 import *
import json

def main():
    days = list(range(1, 21))
    cities = ['Berlin', 'Nice', 'Athens', 'Stockholm', 'Barcelona', 'Vilnius', 'Lyon']
    
    present = {}
    for day in days:
        present[day] = {}
        for city in cities:
            present[day][city] = Bool(f"present_{day}_{city}")
    
    s = Solver()
    
    direct_flights_list = [
        ('Lyon','Nice'), 
        ('Stockholm','Athens'), 
        ('Nice','Athens'), 
        ('Berlin','Athens'), 
        ('Berlin','Nice'), 
        ('Berlin','Barcelona'), 
        ('Berlin','Vilnius'), 
        ('Barcelona','Nice'), 
        ('Athens','Vilnius'), 
        ('Berlin','Stockholm'), 
        ('Nice','Stockholm'), 
        ('Barcelona','Athens'), 
        ('Barcelona','Stockholm'), 
        ('Barcelona','Lyon')
    ]
    direct_flights_set = set()
    for (c1, c2) in direct_flights_list:
        direct_flights_set.add((c1, c2))
        direct_flights_set.add((c2, c1))
    
    for day in days:
        or_conditions = [present[day][city] for city in cities]
        s.add(Or(or_conditions))
        
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                for k in range(j+1, len(cities)):
                    c1, c2, c3 = cities[i], cities[j], cities[k]
                    s.add(Not(And(present[day][c1], present[day][c2], present[day][c3])))
    
    s.add(present[1]['Berlin'] == True)
    s.add(present[3]['Berlin'] == True)
    s.add(present[3]['Barcelona'] == True)
    s.add(present[4]['Barcelona'] == True)
    s.add(present[4]['Lyon'] == True)
    s.add(present[5]['Lyon'] == True)
    
    for city in cities:
        if city != 'Berlin':
            s.add(present[1][city] == False)
    
    s.add(present[2]['Berlin'] == True)
    for city in cities:
        if city not in ['Berlin', 'Barcelona']:
            s.add(present[3][city] == False)
    for city in cities:
        if city not in ['Barcelona', 'Lyon']:
            s.add(present[4][city] == False)
    s.add(present[5]['Nice'] == True)
    for city in cities:
        if city not in ['Lyon', 'Nice']:
            s.add(present[5][city] == False)
    
    total_days = {}
    for city in cities:
        total = 0
        for day in days:
            total += If(present[day][city], 1, 0)
        total_days[city] = total
    s.add(total_days['Berlin'] == 3)
    s.add(total_days['Nice'] == 5)
    s.add(total_days['Athens'] == 5)
    s.add(total_days['Stockholm'] == 5)
    s.add(total_days['Barcelona'] == 2)
    s.add(total_days['Vilnius'] == 4)
    s.add(total_days['Lyon'] == 2)
    
    for day in days:
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                if (c1, c2) not in direct_flights_set:
                    s.add(Not(And(present[day][c1], present[day][c2])))
    
    for city in cities:
        for day in days:
            if day < 20:
                s.add(Implies(
                    And(present[day][city], Not(present[day+1][city])),
                    Or([And(present[day][other], (city, other) in direct_flights_set) for other in cities if other != city])
                ))
            if day > 1:
                s.add(Implies(
                    And(present[day][city], Not(present[day-1][city])),
                    Or([And(present[day][other], (city, other) in direct_flights_set) for other in cities if other != city])
                ))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in days:
            cities_list = []
            for city in cities:
                if m.evaluate(present[day][city], model_completion=True):
                    cities_list.append(city)
            itinerary.append({"day": day, "cities": cities_list})
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()