from z3 import *
import json

def main():
    # Cities mapping: 0=Mykonos, 1=Budapest, 2=Hamburg
    cities = [0, 1, 2]
    city_names = {0: 'Mykonos', 1: 'Budapest', 2: 'Hamburg'}
    
    # Create Z3 variables for start_city for each day (days 1 to 9)
    start_city = [Int('start_city_%d' % d) for d in range(1, 10)]
    
    s = Solver()
    
    # Each day's start city must be one of the three cities
    for i in range(9):
        s.add(Or([start_city[i] == c for c in cities]))
    
    # Flight constraints: if moving between cities, ensure a direct flight exists
    for i in range(8):  # from day1 to day8
        s.add(
            If(
                start_city[i] != start_city[i+1],
                Or(
                    And(start_city[i] == 0, start_city[i+1] == 1),
                    And(start_city[i] == 1, start_city[i+1] == 0),
                    And(start_city[i] == 1, start_city[i+1] == 2),
                    And(start_city[i] == 2, start_city[i+1] == 1)
                ),
                True  # if staying, no constraint
            )
        )
    
    # Constraints for day4: must be in Mykonos
    s.add(Or(
        start_city[3] == 0,  # start in Mykonos on day4
        And(start_city[3] != start_city[4], start_city[4] == 0)  # or fly to Mykonos on day4
    ))
    
    # Constraint for day9: must start in Mykonos
    s.add(start_city[8] == 0)
    
    # Helper function to define presence in a city on a given day
    def in_city(day_index, city):
        if day_index < 8:  # days 1 to 8
            return Or(
                start_city[day_index] == city,
                And(start_city[day_index] != start_city[day_index+1], start_city[day_index+1] == city)
            )
        else:  # day9
            return start_city[day_index] == city
    
    # Total days in Mykonos must be 6
    total_mykonos = Sum([If(in_city(i, 0), 1, 0) for i in range(9)])
    s.add(total_mykonos == 6)
    
    # Total days in Budapest must be 3
    total_budapest = Sum([If(in_city(i, 1), 1, 0) for i in range(9)])
    s.add(total_budapest == 3)
    
    # Total days in Hamburg must be 2
    total_hamburg = Sum([If(in_city(i, 2), 1, 0) for i in range(9)])
    s.add(total_hamburg == 2)
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        start_vals = [m.evaluate(start_city[i]).as_long() for i in range(9)]
        
        itinerary_list = []
        for day in range(1, 10):
            idx = day - 1
            if day < 9:
                if start_vals[idx] != start_vals[idx+1]:
                    cities_on_day = sorted({start_vals[idx], start_vals[idx+1]})
                else:
                    cities_on_day = [start_vals[idx]]
            else:
                cities_on_day = [start_vals[idx]]
            
            city_names_list = [city_names[c] for c in cities_on_day]
            city_names_list_sorted = sorted(city_names_list)  # Sort alphabetically for consistency
            itinerary_list.append({"day": day, "place": city_names_list_sorted})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()