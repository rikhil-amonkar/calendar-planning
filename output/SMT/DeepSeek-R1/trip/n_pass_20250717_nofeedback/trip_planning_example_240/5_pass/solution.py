from z3 import *
import json
from collections import defaultdict

def main():
    cities = ['Prague', 'Berlin', 'Tallinn', 'Stockholm']
    days = list(range(1, 13))
    
    In = {}
    for city in cities:
        In[city] = {day: Bool(f"In_{city}_{day}") for day in days}
    
    s = Solver()
    
    # Fixed constraints
    for day in range(8, 13):
        s.add(In['Tallinn'][day] == True)
    s.add(In['Berlin'][6] == True)
    s.add(In['Berlin'][8] == True)
    
    # Total days per city
    s.add(Sum([If(In['Prague'][day], 1, 0) for day in days]) == 2)
    s.add(Sum([If(In['Berlin'][day], 1, 0) for day in days]) == 3)
    s.add(Sum([If(In['Tallinn'][day], 1, 0) for day in days]) == 5)
    s.add(Sum([If(In['Stockholm'][day], 1, 0) for day in days]) == 5)
    
    # Direct flight connections
    allowed_flights = [
        ("Berlin", "Tallinn"),
        ("Prague", "Tallinn"),
        ("Stockholm", "Tallinn"),
        ("Prague", "Stockholm"),
        ("Stockholm", "Berlin")
    ]
    allowed_pairs = set(tuple(sorted(pair)) for pair in allowed_flights)
    
    # Constraint: 1-2 cities per day
    for day in days:
        cities_present = [In[city][day] for city in cities]
        s.add(Sum([If(c, 1, 0) for c in cities_present]) >= 1)
        s.add(Sum([If(c, 1, 0) for c in cities_present]) <= 2)
    
    # Forbid unconnected cities on same day
    for day in days:
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                A, B = cities[i], cities[j]
                if tuple(sorted((A, B))) not in allowed_pairs:
                    s.add(Not(And(In[A][day], In[B][day])))
    
    # Forbid unconnected transitions between consecutive days
    for day in range(1, 12):
        for A in cities:
            for B in cities:
                if A != B:
                    pair = tuple(sorted((A, B)))
                    if pair not in allowed_pairs:
                        s.add(Not(And(In[A][day], In[B][day+1])))
    
    if s.check() == sat:
        model = s.model()
        city_days = defaultdict(list)
        for city in cities:
            for day in days:
                if is_true(model.eval(In[city][day])):
                    city_days[city].append(day)
        
        # Create contiguous blocks for each city
        blocks = []
        for city, days_list in city_days.items():
            days_list.sort()
            if not days_list:
                continue
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
        
        # Sort blocks by start day
        blocks_sorted = sorted(blocks, key=lambda x: x[1])
        
        # Format itinerary
        itinerary_list = []
        for city, start, end in blocks_sorted:
            day_range = f"Day {start}" if start == end else f"Day {start}-{end}"
            itinerary_list.append({'day_range': day_range, 'place': city})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()