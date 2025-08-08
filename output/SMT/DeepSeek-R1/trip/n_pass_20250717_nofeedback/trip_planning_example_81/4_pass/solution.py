from z3 import *
import json

def main():
    # Cities mapping: 0=Mykonos, 1=Budapest, 2=Hamburg
    city_names = {0: 'Mykonos', 1: 'Budapest', 2: 'Hamburg'}
    
    # Create Z3 variables for start_city for each day (days 1 to 9)
    start_city = [Int('start_city_%d' % d) for d in range(9)]
    
    s = Solver()
    
    # Each day's start city must be one of the three cities
    for i in range(9):
        s.add(Or(start_city[i] == 0, start_city[i] == 1, start_city[i] == 2))
    
    # Flight constraints: if moving between consecutive days, ensure a direct flight exists
    for i in range(8):
        s.add(
            If(
                start_city[i] != start_city[i+1],
                Or(
                    And(start_city[i] == 0, start_city[i+1] == 1),
                    And(start_city[i] == 1, start_city[i+1] == 0),
                    And(start_city[i] == 1, start_city[i+1] == 2),
                    And(start_city[i] == 2, start_city[i+1] == 1)
                ),
                True
            )
        )
    
    # Helper function to check presence in a city on a specific day
    def in_city(day_index, city):
        if day_index < 8:
            return Or(
                start_city[day_index] == city,
                And(start_city[day_index] != start_city[day_index+1], start_city[day_index+1] == city)
            )
        else:
            return start_city[day_index] == city
    
    # Conference day constraints: Must be in Mykonos on day 4 and day 9
    s.add(in_city(3, 0))  # Day 4 (0-indexed day 3)
    s.add(in_city(8, 0))  # Day 9 (0-indexed day 8)
    
    # Total days in each city
    total_mykonos = Sum([If(in_city(i, 0), 1, 0) for i in range(9)])
    total_budapest = Sum([If(in_city(i, 1), 1, 0) for i in range(9)])
    total_hamburg = Sum([If(in_city(i, 2), 1, 0) for i in range(9)])
    
    s.add(total_mykonos == 6)
    s.add(total_budapest == 3)
    s.add(total_hamburg == 2)
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        start_vals = [m.evaluate(start_city[i]).as_long() for i in range(9)]
        
        itinerary_list = []
        for j in range(9):
            day = j + 1
            if j < 8 and start_vals[j] != start_vals[j+1]:
                cities_on_day = [start_vals[j], start_vals[j+1]]
            else:
                cities_on_day = [start_vals[j]]
            city_names_list = [city_names[c] for c in cities_on_day]
            sorted_cities = sorted(city_names_list)
            itinerary_list.append({"day": day, "place": sorted_cities})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()