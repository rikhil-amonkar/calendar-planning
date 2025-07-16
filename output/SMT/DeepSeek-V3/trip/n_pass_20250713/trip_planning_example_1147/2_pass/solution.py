from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Brussels', 'Helsinki', 'Split', 'Dubrovnik', 'Istanbul', 'Milan', 'Vilnius', 'Frankfurt']
    # Mapping for easier reference
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: list of tuples (from, to)
    direct_flights = [
        ('Milan', 'Frankfurt'), ('Split', 'Frankfurt'), ('Milan', 'Split'),
        ('Brussels', 'Vilnius'), ('Brussels', 'Helsinki'), ('Istanbul', 'Brussels'),
        ('Milan', 'Vilnius'), ('Brussels', 'Milan'), ('Istanbul', 'Helsinki'),
        ('Helsinki', 'Vilnius'), ('Helsinki', 'Dubrovnik'), ('Split', 'Vilnius'),
        ('Dubrovnik', 'Istanbul'), ('Istanbul', 'Milan'), ('Helsinki', 'Frankfurt'),
        ('Istanbul', 'Vilnius'), ('Split', 'Helsinki'), ('Milan', 'Helsinki'),
        ('Istanbul', 'Frankfurt'), ('Brussels', 'Frankfurt'), ('Dubrovnik', 'Frankfurt'),
        ('Frankfurt', 'Vilnius')
    ]
    
    # Create a set of possible transitions (both directions)
    flight_pairs = set()
    for (f, t) in direct_flights:
        flight_pairs.add((f, t))
        flight_pairs.add((t, f))
    
    # Days are 1..22
    days = 22
    # Create a solver instance
    s = Solver()
    
    # Variables: day[i] is the city on day i (1-based)
    day_city = [Int(f'day_{i}') for i in range(1, days+1)]
    
    # Each day_city must be between 0 and 7 (representing the cities)
    for i in range(days):
        s.add(day_city[i] >= 0, day_city[i] < 8)
    
    # Fixed constraints:
    # Istanbul from day 1 to 5
    for i in range(5):  # days 1-5 (0-based 0-4)
        s.add(day_city[i] == city_map['Istanbul'])
    
    # Vilnius between day 18 to 22 (days 17-21 in 0-based)
    for i in range(17, 22):
        s.add(day_city[i] == city_map['Vilnius'])
    
    # Frankfurt must be visited between day 16-18 (days 15-17 in 0-based)
    s.add(Or(
        day_city[15] == city_map['Frankfurt'],
        day_city[16] == city_map['Frankfurt'],
        day_city[17] == city_map['Frankfurt']
    ))
    
    # Flight constraints: consecutive days must be same city or have a direct flight
    for i in range(days - 1):
        current_city = day_city[i]
        next_city = day_city[i+1]
        # Either same city or a direct flight
        s.add(Or(
            current_city == next_city,
            # Check if there's a flight between current_city and next_city
            *[
                And(current_city == city_map[f], next_city == city_map[t])
                for (f, t) in flight_pairs
            ]
        ))
    
    # Total days per city constraints
    # Brussels: 3
    s.add(Sum([If(day_city[i] == city_map['Brussels'], 1, 0) for i in range(days)]) == 3)
    # Helsinki: 3
    s.add(Sum([If(day_city[i] == city_map['Helsinki'], 1, 0) for i in range(days)]) == 3)
    # Split: 4
    s.add(Sum([If(day_city[i] == city_map['Split'], 1, 0) for i in range(days)]) == 4)
    # Dubrovnik: 2
    s.add(Sum([If(day_city[i] == city_map['Dubrovnik'], 1, 0) for i in range(days)]) == 2)
    # Istanbul: 5 (already 5 days fixed)
    s.add(Sum([If(day_city[i] == city_map['Istanbul'], 1, 0) for i in range(days)]) == 5)
    # Milan: 4
    s.add(Sum([If(day_city[i] == city_map['Milan'], 1, 0) for i in range(days)]) == 4)
    # Vilnius: 5 (already 5 days fixed)
    s.add(Sum([If(day_city[i] == city_map['Vilnius'], 1, 0) for i in range(days)]) == 5)
    # Frankfurt: 3
    s.add(Sum([If(day_city[i] == city_map['Frankfurt'], 1, 0) for i in range(days)]) == 3)
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        # Generate the itinerary
        current_place = None
        start_day = 1
        for day in range(1, days + 1):
            city_idx = model.evaluate(day_city[day - 1]).as_long()
            city = cities[city_idx]
            if current_place is None:
                current_place = city
                start_day = day
            elif city != current_place:
                # Add the previous stay
                if start_day == day - 1:
                    itinerary.append({'day_range': f'Day {start_day}', 'place': current_place})
                else:
                    itinerary.append({'day_range': f'Day {start_day}-{day - 1}', 'place': current_place})
                # Add the flight day (current_place and city)
                itinerary.append({'day_range': f'Day {day}', 'place': current_place})
                itinerary.append({'day_range': f'Day {day}', 'place': city})
                current_place = city
                start_day = day
        # Add the last stay
        if start_day == days:
            itinerary.append({'day_range': f'Day {start_day}', 'place': current_place})
        else:
            itinerary.append({'day_range': f'Day {start_day}-{days}', 'place': current_place})
        
        # Verify that the itinerary meets all constraints
        # (This is a sanity check; the model should already satisfy them)
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
print(json.dumps(result, indent=2))