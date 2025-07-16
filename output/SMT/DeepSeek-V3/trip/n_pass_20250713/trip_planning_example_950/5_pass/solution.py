from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Rome', 'Mykonos', 'Riga', 'Munich', 'Bucharest', 'Nice', 'Krakow']
    
    # Direct flights as a set of tuples
    direct_flights = {
        ('Nice', 'Riga'), ('Riga', 'Nice'),
        ('Bucharest', 'Munich'), ('Munich', 'Bucharest'),
        ('Mykonos', 'Munich'), ('Munich', 'Mykonos'),
        ('Riga', 'Bucharest'), ('Bucharest', 'Riga'),
        ('Rome', 'Nice'), ('Nice', 'Rome'),
        ('Rome', 'Munich'), ('Munich', 'Rome'),
        ('Mykonos', 'Nice'), ('Nice', 'Mykonos'),
        ('Rome', 'Mykonos'), ('Mykonos', 'Rome'),
        ('Munich', 'Krakow'), ('Krakow', 'Munich'),
        ('Rome', 'Bucharest'), ('Bucharest', 'Rome'),
        ('Nice', 'Munich'), ('Munich', 'Nice'),
        ('Riga', 'Munich'), ('Munich', 'Riga'),
        ('Rome', 'Riga'), ('Riga', 'Rome')
    }
    
    # Create a Z3 solver instance
    s = Solver()
    
    # Variables: day_1 to day_17, each can be one of the cities
    days = [Int(f'day_{i}') for i in range(1, 18)]
    
    # Each day variable must be between 0 and 6 (representing the cities)
    for i in range(17):
        s.add(days[i] >= 0, days[i] < len(cities))
    
    # Helper function to get city index
    def city_index(city):
        return cities.index(city)
    
    # Constraints
    
    # 1. Rome days 1-4 (conference)
    s.add(days[0] == city_index('Rome'))  # Day 1
    s.add(days[1] == city_index('Rome'))  # Day 2
    s.add(days[2] == city_index('Rome'))  # Day 3
    s.add(days[3] == city_index('Rome'))  # Day 4
    
    # 2. Mykonos for 3 days, with wedding between day 4-6 (so at least one day in 4-6 is Mykonos)
    mykonos_days = [If(days[i] == city_index('Mykonos'), 1, 0) for i in range(17)]
    s.add(sum(mykonos_days) == 3)
    s.add(Or([days[i] == city_index('Mykonos') for i in [3, 4, 5]]))  # days 4,5,6 (0-based 3,4,5)
    
    # Riga: 3 days
    riga_days = [If(days[i] == city_index('Riga'), 1, 0) for i in range(17)]
    s.add(sum(riga_days) == 3)
    
    # Munich: 4 days
    munich_days = [If(days[i] == city_index('Munich'), 1, 0) for i in range(17)]
    s.add(sum(munich_days) == 4)
    
    # Bucharest: 4 days
    bucharest_days = [If(days[i] == city_index('Bucharest'), 1, 0) for i in range(17)]
    s.add(sum(bucharest_days) == 4)
    
    # Rome: total 4 days (already 4 days from day 1-4)
    rome_days = [If(days[i] == city_index('Rome'), 1, 0) for i in range(17)]
    s.add(sum(rome_days) == 4)
    
    # Nice: 3 days
    nice_days = [If(days[i] == city_index('Nice'), 1, 0) for i in range(17)]
    s.add(sum(nice_days) == 3)
    
    # Krakow: 2 days, days 16-17 (indices 15-16)
    s.add(days[15] == city_index('Krakow'))  # Day 16
    s.add(days[16] == city_index('Krakow'))  # Day 17
    
    # Flight constraints: consecutive days can only change to cities with direct flights.
    for i in range(16):
        current_city = days[i]
        next_city = days[i+1]
        # If changing cities, the pair must be in direct_flights.
        s.add(If(current_city != next_city,
                 Or([And(current_city == city_index(a), next_city == city_index(b)) 
                     for (a, b) in direct_flights if a in cities and b in cities]),
                 True))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        day_assignments = []
        for i in range(17):
            day = i + 1
            city_idx = m.evaluate(days[i]).as_long()
            city = cities[city_idx]
            day_assignments.append(city)
        
        # Generate the itinerary
        itinerary = []
        current_city = day_assignments[0]
        start_day = 1
        
        for day in range(1, 18):
            if day == 1:
                continue
            
            if day_assignments[day-1] != current_city:
                # Add the stay up to day-1
                if start_day == day - 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day-1}", "place": current_city})
                # Add the flight day (day-1 is the departure, day is the arrival)
                itinerary.append({"day_range": f"Day {day-1}", "place": current_city})
                itinerary.append({"day_range": f"Day {day-1}", "place": day_assignments[day-1]})
                current_city = day_assignments[day-1]
                start_day = day
        
        # Add the last stay
        if start_day <= 17:
            if start_day == 17:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
            else:
                itinerary.append({"day_range": f"Day {start_day}-17", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))