from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Mykonos', 'Nice', 'London', 'Copenhagen', 'Oslo', 'Tallinn']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: list of tuples (from, to)
    direct_flights = [
        ('London', 'Copenhagen'), ('Copenhagen', 'Tallinn'), 
        ('Tallinn', 'Oslo'), ('Mykonos', 'London'), 
        ('Oslo', 'Nice'), ('London', 'Nice'), 
        ('Mykonos', 'Nice'), ('London', 'Oslo'), 
        ('Copenhagen', 'Nice'), ('Copenhagen', 'Oslo')
    ]
    # Make it bidirectional
    bidirectional = []
    for (a, b) in direct_flights:
        bidirectional.append((a, b))
        bidirectional.append((b, a))
    direct_flights = bidirectional
    flight_pairs = set((city_map[a], city_map[b]) for (a, b) in direct_flights)
    
    # Days
    days_total = 16
    days = list(range(1, days_total + 1))
    
    # Z3 variables: for each day, which city (index)
    city_vars = [Int(f'day_{day}') for day in days]
    
    s = Solver()
    
    # Each day variable must be a valid city index (0 to 5)
    for day_var in city_vars:
        s.add(day_var >= 0, day_var < len(cities))
    
    # Constraints for total days in each city
    total_days = {
        'Mykonos': 4,
        'Nice': 3,
        'London': 2,
        'Copenhagen': 3,
        'Oslo': 5,
        'Tallinn': 4
    }
    
    for city, count in total_days.items():
        city_idx = city_map[city]
        s.add(Sum([If(city_vars[day] == city_idx, 1, 0) for day in range(days_total)]) == count)
    
    # Fixed constraints:
    # Nice on days 14,15,16 (indices 13,14,15)
    for day in [13, 14, 15]:
        s.add(city_vars[day] == city_map['Nice'])
    
    # Oslo between day 10 and 14 (days 9 to 13 in 0-based)
    # At least one day in Oslo between 10-14 (days 9-13 in 0-based)
    s.add(Or([city_vars[day] == city_map['Oslo'] for day in range(9, 14)]))
    
    # Flight transitions: consecutive days must be connected by a direct flight or same city
    for i in range(days_total - 1):
        current = city_vars[i]
        next_ = city_vars[i + 1]
        s.add(Or(
            current == next_,
            *[And(current == a, next_ == b) for (a, b) in flight_pairs]
        ))
    
    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        # Generate the day sequence
        day_sequence = []
        for day in range(days_total):
            city_idx = m.evaluate(city_vars[day]).as_long()
            day_sequence.append(cities[city_idx])
        
        # Now, process the sequence to create the itinerary with flight days
        current_place = day_sequence[0]
        start_day = 1
        for day in range(1, days_total):
            if day_sequence[day] != current_place:
                # Flight day
                end_day = day
                if start_day == end_day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_place})
                itinerary.append({"day_range": f"Day {day + 1}", "place": current_place})
                itinerary.append({"day_range": f"Day {day + 1}", "place": day_sequence[day]})
                current_place = day_sequence[day]
                start_day = day + 1
        # Add the last stay
        if start_day <= days_total:
            if start_day == days_total:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{days_total}", "place": current_place})
        
        # Now, create the JSON output
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No valid itinerary found.")

solve_itinerary()