from z3 import *

def solve_itinerary():
    s = Solver()

    # Days 1-12
    days = 12
    Day = list(range(1, days+1))

    # Cities
    Milan, Seville, Naples = 0, 1, 2
    cities = ['Milan', 'Seville', 'Naples']

    # Flight connections
    connections = {
        (Milan, Seville),
        (Seville, Milan),
        (Naples, Milan),
        (Milan, Naples)
    }

    # Variables for each day's city
    city_vars = [Int(f'city_{d}') for d in Day]

    # Each day must be one of the cities
    for d in Day:
        s.add(Or([city_vars[d-1] == c for c in [Milan, Seville, Naples]]))

    # Flight constraints between consecutive days
    for d in range(1, days):
        current = city_vars[d-1]
        next_c = city_vars[d]
        s.add(Implies(current != next_c, 
                     Or([And(current == a, next_c == b) for (a,b) in connections])))

    # Total days in each city
    total_milan = sum([If(city_vars[d-1] == Milan, 1, 0) for d in Day])
    total_seville = sum([If(city_vars[d-1] == Seville, 1, 0) for d in Day])
    total_naples = sum([If(city_vars[d-1] == Naples, 1, 0) for d in Day])

    s.add(total_milan == 7)
    s.add(total_seville == 4)
    s.add(total_naples == 3)

    # Seville must be days 9-12
    for d in range(9, 13):
        s.add(city_vars[d-1] == Seville)

    # Check solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        day_cities = [model.evaluate(city_vars[d-1]).as_long() for d in Day]
        
        # Build itinerary with flight days
        current_place = cities[day_cities[0]]
        start_day = 1
        for d in range(2, days+1):
            if day_cities[d-1] != day_cities[d-2]:
                # Add stay before flight
                if start_day == d-1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{d-1}", "place": current_place})
                # Add flight day (both cities)
                itinerary.append({"day_range": f"Day {d-1}", "place": current_place})
                next_place = cities[day_cities[d-1]]
                itinerary.append({"day_range": f"Day {d-1}", "place": next_place})
                current_place = next_place
                start_day = d
        # Add final stay
        if start_day == days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{days}", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate itinerary
itinerary = solve_itinerary()
print(itinerary)