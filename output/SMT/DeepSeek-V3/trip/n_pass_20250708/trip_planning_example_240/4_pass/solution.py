from z3 import *

def solve_itinerary():
    # Cities
    Prague, Berlin, Tallinn, Stockholm = Ints('Prague Berlin Tallinn Stockholm')
    cities = {'Prague': 0, 'Berlin': 1, 'Tallinn': 2, 'Stockholm': 3}
    inv_cities = {v: k for k, v in cities.items()}
    
    # Direct flights: list of tuples
    direct_flights = [
        (0, 2), (2, 0),  # Prague <-> Tallinn
        (0, 3), (3, 0),   # Prague <-> Stockholm
        (1, 2), (2, 1),   # Berlin <-> Tallinn
        (1, 3), (3, 1),   # Berlin <-> Stockholm
        (2, 3), (3, 2)    # Tallinn <-> Stockholm
    ]
    
    s = Solver()
    
    # Variables for each day's city
    day_city = [Int(f'day_{i}_city') for i in range(1, 13)]
    
    # Each day_city must be 0, 1, 2, or 3
    for dc in day_city:
        s.add(Or([dc == c for c in range(4)]))
    
    # Constraints on city days:
    # Prague: 2 days
    # Berlin: 3 days, must include days 6 and 8
    # Tallinn: 5 days, must include days 8-12
    # Stockholm: 5 days
    
    # Count days per city
    prague_days = Sum([If(dc == cities['Prague'], 1, 0) for dc in day_city])
    berlin_days = Sum([If(dc == cities['Berlin'], 1, 0) for dc in day_city])
    tallinn_days = Sum([If(dc == cities['Tallinn'], 1, 0) for dc in day_city])
    stockholm_days = Sum([If(dc == cities['Stockholm'], 1, 0) for dc in day_city])
    
    s.add(prague_days == 2)
    s.add(berlin_days == 3)
    s.add(tallinn_days == 5)
    s.add(stockholm_days == 5)
    
    # Berlin must include days 6 and 8 (indices 5 and 7 in 0-based)
    s.add(day_city[5] == cities['Berlin'])
    s.add(day_city[7] == cities['Berlin'])
    
    # Tallinn must be visited between days 8-12 (indices 7..11 in 0-based)
    s.add(Sum([If(day_city[i] == cities['Tallinn'], 1, 0) for i in range(7, 12)]) >= 1)
    
    # Flight constraints: consecutive different cities must be connected by a direct flight
    for i in range(11):
        current_city = day_city[i]
        next_city = day_city[i+1]
        s.add(If(current_city != next_city,
                 Or([And(current_city == c1, next_city == c2) for (c1, c2) in direct_flights]),
                 True))
    
    # Try to find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current_city = None
        start_day = 1
        for day in range(1, 13):
            city_idx = m.evaluate(day_city[day-1]).as_long()
            city = inv_cities[city_idx]
            if day == 1:
                current_city = city
                start_day = 1
            else:
                prev_city_idx = m.evaluate(day_city[day-2]).as_long()
                if city_idx != prev_city_idx:
                    # Flight day: day is in both cities
                    prev_city = inv_cities[prev_city_idx]
                    itinerary.append({"day_range": f"Day {start_day}-{day-1}", "place": prev_city})
                    itinerary.append({"day_range": f"Day {day-1}", "place": prev_city})
                    itinerary.append({"day_range": f"Day {day-1}", "place": city})
                    start_day = day
                    current_city = city
        # Add the last stay
        itinerary.append({"day_range": f"Day {start_day}-12", "place": current_city})
        
        # Post-process to merge consecutive days in the same city
        merged_itinerary = []
        i = 0
        n = len(itinerary)
        while i < n:
            entry = itinerary[i]
            if i < n - 1 and itinerary[i]['place'] == itinerary[i+1]['place']:
                # Merge consecutive entries
                start_day = int(entry['day_range'].split('-')[0][4:])
                next_entry = itinerary[i+1]
                next_day = int(next_entry['day_range'].split('-')[-1][4:])
                merged_entry = {"day_range": f"Day {start_day}-{next_day}", "place": entry['place']}
                merged_itinerary.append(merged_entry)
                i += 2
            else:
                merged_itinerary.append(entry)
                i += 1
        return {"itinerary": merged_itinerary}
    else:
        return {"error": "No valid itinerary found"}

def main():
    solution = solve_itinerary()
    print(solution)

if __name__ == "__main__":
    main()