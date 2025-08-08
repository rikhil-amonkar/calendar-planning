from z3 import *
import json

def main():
    cities = ['Prague', 'Berlin', 'Tallinn', 'Stockholm']
    days = list(range(1, 13))
    
    In = {}
    for city in cities:
        In[city] = {day: Bool(f"In_{city}_{day}") for day in days}
    
    s = Solver()
    
    for day in range(8, 13):
        s.add(In['Tallinn'][day] == True)
    
    s.add(In['Berlin'][6] == True)
    s.add(In['Berlin'][8] == True)
    
    s.add(Sum([If(In['Prague'][day], 1, 0) for day in days]) == 2)
    s.add(Sum([If(In['Berlin'][day], 1, 0) for day in days]) == 3)
    s.add(Sum([If(In['Tallinn'][day], 1, 0) for day in days]) == 5)
    s.add(Sum([If(In['Stockholm'][day], 1, 0) for day in days]) == 5)
    
    allowed_flights = [
        "Berlin and Tallinn",
        "Prague and Tallinn",
        "Stockholm and Tallinn",
        "Prague and Stockholm",
        "Stockholm and Berlin"
    ]
    allowed_pairs = set()
    for flight in allowed_flights:
        parts = flight.split(' and ')
        sorted_pair = tuple(sorted(parts))
        allowed_pairs.add(sorted_pair)
    
    for day in days:
        cities_present = [In[city][day] for city in cities]
        s.add(Sum([If(c, 1, 0) for c in cities_present]) == 1)
    
    for i in range(1, 12):
        for A in cities:
            for B in cities:
                if A != B:
                    pair = tuple(sorted([A, B]))
                    if pair not in allowed_pairs:
                        s.add(Not(And(In[A][i], In[B][i+1])))
    
    if s.check() == sat:
        model = s.model()
        city_days = {}
        for city in cities:
            city_days[city] = []
            for day in days:
                if is_true(model.eval(In[city][day])):
                    city_days[city].append(day)
        
        blocks = []
        for city, days_list in city_days.items():
            if not days_list:
                continue
            days_list.sort()
            start = days_list[0]
            end = days_list[0]
            for i in range(1, len(days_list)):
                if days_list[i] == end + 1:
                    end = days_list[i]
                else:
                    blocks.append((city, start, end))
                    start = days_list[i]
                    end = days_list[i]
            blocks.append((city, start, end))
        
        blocks_sorted = sorted(blocks, key=lambda x: x[1])
        
        itinerary_list = []
        for (city, start, end) in blocks_sorted:
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary_list.append({'day_range': day_range, 'place': city})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()