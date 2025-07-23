from z3 import *
import json

def main():
    cities = ['Hamburg', 'Zurich', 'Helsinki', 'Bucharest', 'Split']
    required_days = {
        'Hamburg': 2,
        'Zurich': 3,
        'Helsinki': 2,
        'Bucharest': 2,
        'Split': 7
    }
    
    flight_list = [
        ('Zurich', 'Helsinki'),
        ('Hamburg', 'Bucharest'),
        ('Helsinki', 'Hamburg'),
        ('Zurich', 'Hamburg'),
        ('Zurich', 'Bucharest'),
        ('Zurich', 'Split'),
        ('Helsinki', 'Split'),
        ('Split', 'Hamburg')
    ]
    
    flight_set = {frozenset({c1, c2}) for (c1, c2) in flight_list}
    
    disallowed_pairs = set()
    for i in range(len(cities)):
        for j in range(i+1, len(cities)):
            c1 = cities[i]
            c2 = cities[j]
            pair = frozenset({c1, c2})
            if pair not in flight_set:
                disallowed_pairs.add((c1, c2))
    
    days = list(range(1, 13))
    s = Solver()
    
    In = {}
    for city in cities:
        In[city] = {}
        for d in days:
            In[city][d] = Bool(f"In_{city}_{d}")
    
    for d in days:
        s.add(Or([In[city][d] for city in cities]))
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                for k in range(j+1, len(cities)):
                    c1, c2, c3 = cities[i], cities[j], cities[k]
                    s.add(Not(And(In[c1][d], In[c2][d], In[c3][d])))
    
    for city in cities:
        total = 0
        for d in days:
            total += If(In[city][d], 1, 0)
        s.add(total == required_days[city])
    
    for d in days:
        for (c1, c2) in disallowed_pairs:
            s.add(Not(And(In[c1][d], In[c2][d])))
    
    for d in range(1, 12):
        common_cities = []
        for city in cities:
            common_cities.append(And(In[city][d], In[city][d+1]))
        s.add(Or(common_cities))
    
    s.add(In['Split'][4] == True)
    s.add(In['Split'][10] == True)
    s.add(Or(In['Zurich'][1], In['Zurich'][2], In['Zurich'][3]))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for d in days:
            cities_today = []
            for city in cities:
                if m.evaluate(In[city][d], model_completion=True):
                    cities_today.append(city)
            if len(cities_today) == 1:
                city_str = cities_today[0]
            else:
                cities_today_sorted = sorted(cities_today)
                city_str = " and ".join(cities_today_sorted)
            itinerary.append({"day": d, "city": city_str})
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()