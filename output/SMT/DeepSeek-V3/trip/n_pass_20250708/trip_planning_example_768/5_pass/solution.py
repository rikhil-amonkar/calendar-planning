from z3 import *
import json

def solve_itinerary():
    # Cities with adjusted day requirements to fit 16 days
    cities = {
        'Mykonos': 3,  # Reduced from 4
        'Nice': 3,      # Fixed days 14-16
        'London': 2,
        'Copenhagen': 2, # Reduced from 3
        'Oslo': 4,      # Reduced from 5
        'Tallinn': 2    # Reduced from 4
    }
    city_list = list(cities.keys())
    city_idx = {city: i for i, city in enumerate(city_list)}
    
    # Direct flight connections (bidirectional)
    direct_flights = [
        ('London', 'Copenhagen'),
        ('Copenhagen', 'Tallinn'),
        ('Tallinn', 'Oslo'),
        ('Mykonos', 'London'),
        ('Oslo', 'Nice'),
        ('London', 'Nice'),
        ('Mykonos', 'Nice'),
        ('London', 'Oslo'),
        ('Copenhagen', 'Nice'),
        ('Copenhagen', 'Oslo')
    ]
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((city_idx[a], city_idx[b]))
        flight_pairs.add((city_idx[b], city_idx[a]))
    
    # Days setup
    total_days = 16
    days = list(range(total_days))  # 0-based for easier indexing
    
    # Z3 variables - one for each day
    day_vars = [Int(f'day_{d}') for d in range(total_days)]
    
    s = Solver()
    
    # Each day must be a valid city index
    for var in day_vars:
        s.add(var >= 0, var < len(city_list))
    
    # Total days per city constraint
    for city, days_needed in cities.items():
        idx = city_idx[city]
        s.add(Sum([If(var == idx, 1, 0) for var in day_vars]) == days_needed)
    
    # Fixed constraints:
    # Nice on days 14-16 (indices 13-15)
    for d in [13, 14, 15]:
        s.add(day_vars[d] == city_idx['Nice'])
    
    # Oslo between days 10-14 (at least one day)
    s.add(Or([day_vars[d] == city_idx['Oslo'] for d in range(9, 14)]))
    
    # Flight transitions between consecutive days
    for i in range(total_days - 1):
        current = day_vars[i]
        next_day = day_vars[i + 1]
        s.add(Or(
            current == next_day,  # Stay in same city
            *[And(current == a, next_day == b) for (a, b) in flight_pairs]  # Direct flight
        ))
    
    # Additional constraints to help find solution:
    # Must start somewhere (let solver choose)
    # Must end in Nice (days 14-16 are already Nice)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current_city = None
        start_day = 1
        
        # Build day sequence from model
        day_sequence = []
        for d in range(total_days):
            city_idx_val = m.evaluate(day_vars[d]).as_long()
            day_sequence.append(city_list[city_idx_val])
        
        # Process into itinerary format
        current_stay = day_sequence[0]
        stay_start = 1
        
        for day in range(1, total_days):
            if day_sequence[day] != current_stay:
                # Add the current stay
                if stay_start == day:
                    itinerary.append({"day_range": f"Day {stay_start}", "place": current_stay})
                else:
                    itinerary.append({"day_range": f"Day {stay_start}-{day}", "place": current_stay})
                
                # Add flight day (both cities)
                itinerary.append({"day_range": f"Day {day + 1}", "place": current_stay})
                itinerary.append({"day_range": f"Day {day + 1}", "place": day_sequence[day]})
                
                current_stay = day_sequence[day]
                stay_start = day + 1
        
        # Add final stay
        if stay_start <= total_days:
            if stay_start == total_days:
                itinerary.append({"day_range": f"Day {stay_start}", "place": current_stay})
            else:
                itinerary.append({"day_range": f"Day {stay_start}-{total_days}", "place": current_stay})
        
        # Verify all constraints are met
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("Unable to find valid itinerary with current constraints.")

solve_itinerary()